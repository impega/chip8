{-# OPTIONS  -Wall            #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}

module VirtualMachine where


import Data.Bits
import Data.Word
import Data.Words
import Data.Word8.Arithmetic  as DW8
import Data.Word16.Arithmetic as DWF
import Data.Vector            as Vec
import Control.Applicative
import Control.Monad.Except   as CME
import Control.Monad.State    as CMS
import Control.Monad.Random   as CMR

type Address = Word16
type CnstVal = Word8
type RgstNum = Word8 --only using low 4 bits

data VM =
  VM { memory :: Vector Word8   -- 4096
     , rgsts  :: Vector Word8   -- 16
     , stack  :: Vector Address -- 16
     , keys   :: Vector Bool    -- 16
     , i      :: Address
     , pc     :: Address
     , sp     :: Word8
     , delay  :: Word8
     , sound  :: Word8 }

data LateEffect = Some | None

data OpCode a where
  Op0NNN :: Address ->            OpCode None -- Calls RCA 1802 program at NNN
  Op00E0 ::                       OpCode Some -- ✓ Clears the screen
  Op00EE ::                       OpCode None -- ✓ Returns from a subroutine.
  Op1NNN :: Address            -> OpCode None -- ✓ Jmp NNN
  Op2NNN :: Address            -> OpCode None -- ✓ Calls subroutine at NNN
  Op3XNN :: RgstNum -> CnstVal -> OpCode Some -- ✓ Skips <== VX == NN
  Op4XNN :: RgstNum -> CnstVal -> OpCode Some -- ✓ Skips <== VX <> NN
  Op5XY0 :: RgstNum -> RgstNum -> OpCode Some -- ✓ Skips <== VX == VY
  Op6XNN :: RgstNum -> CnstVal -> OpCode None -- ✓ VX    := NN
  Op7XNN :: RgstNum -> CnstVal -> OpCode None -- ✓ VX   +:= NN
  Op8XY0 :: RgstNum -> RgstNum -> OpCode None -- ✓ VX    := VY
  Op8XY1 :: RgstNum -> RgstNum -> OpCode None -- ✓ VX  or:= VY
  Op8XY2 :: RgstNum -> RgstNum -> OpCode None -- ✓ VX and:= VY
  Op8XY3 :: RgstNum -> RgstNum -> OpCode None -- ✓ VX xor:= VY
  Op8XY4 :: RgstNum -> RgstNum -> OpCode None -- ✓ VX   +:= VY; VF := carry
  Op8XY5 :: RgstNum -> RgstNum -> OpCode None -- ✓ VX   -:= VY; VF := borrow
  Op8XY6 :: RgstNum            -> OpCode None -- ✓ SHR VX; VF := least significant bit
  Op8XY7 :: RgstNum -> RgstNum -> OpCode None -- ✓ VX    := VY - VX; VF := not borrow
  Op8XYE :: RgstNum            -> OpCode None -- ✓ SHL VX; VF := most significant bit
  Op9XY0 :: RgstNum -> RgstNum -> OpCode Some -- ✓ Skips <== VX <> VY
  OpANNN :: Address            -> OpCode None -- ✓ I := NNN
  OpBNNN :: Address            -> OpCode None -- ✓ Jmp NNN + V0
  OpCXNN :: RgstNum -> CnstVal -> OpCode None -- ✓ VX := ?! and NN
--  OpDXYN  Address Address -- Sprites stored in memory at location in index register (I), maximum 8bits wide. Wraps around the screen. If when drawn, clears a pixel, register VF is set to 1 otherwise it is zero. All drawing is XOR drawing (i.e. it toggles the screen pixels)
  OpEX9E :: RgstNum            -> OpCode Some -- ✓ Skips <== VX key     pressed
  OpEXA1 :: RgstNum            -> OpCode Some -- ✓ Skips <== VX key not pressed
  OpFX07 :: RgstNum            -> OpCode None -- ✓ VX := delay
  OpFX0A :: RgstNum            -> OpCode Some -- Locks; VX := next pressed key
  OpFX15 :: RgstNum            -> OpCode None -- ✓ delay  := VX
  OpFX18 :: RgstNum            -> OpCode None -- ✓ sound  := VX
  OpFX1E :: RgstNum            -> OpCode None -- ✓ I     +:= VX; VF := carry
--  | OpFX29  Adress          -- Sets I to the location of the sprite for the character in VX. Characters 0-F (in hexadecimal) are represented by a 4x5 font.
--  | OpFX33  Stores the Binary-coded decimal representation of VX, with the most significant of three digits at the address in I, the middle digit at I plus 1, and the least significant digit at I plus 2.   | Op
  OpFX55 :: RgstNum            -> OpCode None -- ✓ mem[I..I+X] <- (V0,..,VX)
  OpFX65 :: RgstNum            -> OpCode None -- ✓ (V0,..,VX) <- mem[I..I+X]

data Action =
    ClearScreen
  | SkipNext
  | WaitForKey

data RTError =
    StackUnderflow
  | StackOverflow

type family ResultingAction a where
  ResultingAction Some = Maybe Action
  ResultingAction None = ()

jmpTo :: MonadState VM m => Address -> m ()
jmpTo add = CMS.modify $ \ r -> r { pc = add }

setI :: MonadState VM m => Address -> m ()
setI add = CMS.modify $ \ r -> r { i = add }

setDelay :: MonadState VM m => Word8 -> m ()
setDelay val = CMS.modify $ \ r -> r { delay = val }

setSound :: MonadState VM m => Word8 -> m ()
setSound val = CMS.modify $ \ r -> r { sound = val }

setRgst :: MonadState VM m => RgstNum -> Word8 -> m ()
setRgst vx nn = CMS.modify $ \ r -> r { rgsts = rgsts r // mods }
  where mods = [(fromIntegral vx, nn)]

incrIByRgstWithFlag :: (Functor m, Applicative m, MonadState VM m) =>
                       RgstNum -> m ()
incrIByRgstWithFlag vx =
  DWF.addWithCarry <$> CMS.gets i <*> (embed <$> getRgst vx) >>= \ (val, f) ->
  setRgst 0xF (if f then 1 else 0) >>
  setI val

opRgstsWithFlag :: (Functor m, Applicative m, MonadState VM m) =>
                   (Word8 -> Word8 -> (Word8, Bool)) ->
                   RgstNum -> RgstNum -> RgstNum -> m ()
opRgstsWithFlag op vz vx vy =
  op <$> getRgst vx <*> getRgst vy >>= \ (nn, f) ->
  setRgst 0xF (if f then 1 else 0) >>
  setRgst vz nn

getRgst :: MonadState VM m => RgstNum -> m Word8
getRgst vx = CMS.gets $ (! fromIntegral vx) . rgsts

skipNextIf :: MonadState VM m => Bool -> m (Maybe Action)
skipNextIf b = return $ if b then Just SkipNext
                             else Nothing

callSub :: (MonadState VM m, MonadError RTError m) => Address -> Word8 -> m ()
callSub add csp | csp >= 15 = throwError StackOverflow
                | otherwise = do
  cpc <- CMS.gets pc
  ()  <- CMS.modify $ \ r -> r { stack = stack r // [(fromIntegral csp+1, cpc+1)]
                               , sp    = csp + 1 }
  jmpTo add

retSub :: (Functor m, MonadState VM m, MonadError RTError m) => Word8 -> m ()
retSub csp | csp <= 0  = throwError StackUnderflow
           | otherwise = do
  let nsp = csp - 1
  npc <- (! fromIntegral nsp) <$> CMS.gets stack
  ()  <- CMS.modify $ \ r -> r { sp = nsp }
  jmpTo npc

readFromMem :: (Functor m, MonadState VM m) => RgstNum -> m ()
readFromMem vx = do
  begin <- fromIntegral <$> CMS.gets i
  mem   <- CMS.gets memory
  let updates = [ (x, mem ! (begin + x)) | x <- [0..(fromIntegral vx)] ]
  CMS.modify $ \ r -> r { rgsts = rgsts r // updates }

writeToMem :: (Functor m, MonadState VM m) => RgstNum -> m ()
writeToMem vx = do
  begin <- fromIntegral <$> CMS.gets i
  regs  <- CMS.gets rgsts
  let updates = [ (begin + x, regs ! x) | x <- [0..(fromIntegral vx)] ]
  CMS.modify $ \ r -> r { memory = memory r // updates }

opCodeSem ::
  (Functor m, Applicative m, MonadState VM m, MonadRandom m, MonadError RTError m) =>
  OpCode a -> m (ResultingAction a)
opCodeSem Op00E0         = return $ Just ClearScreen
opCodeSem Op00EE         = retSub =<< CMS.gets sp
opCodeSem (Op1NNN add)   = jmpTo add
opCodeSem (Op2NNN add)   = callSub add =<< CMS.gets sp
opCodeSem (Op3XNN vx nn) = skipNextIf =<< (nn ==) <$> getRgst vx
opCodeSem (Op4XNN vx nn) = skipNextIf =<< (nn /=) <$> getRgst vx
opCodeSem (Op5XY0 vx vy) = skipNextIf =<< (==)    <$> getRgst vx <*> getRgst vy
opCodeSem (Op6XNN vx nn) = setRgst vx nn
opCodeSem (Op7XNN vx nn) = setRgst vx =<< (nn +)  <$> getRgst vx
opCodeSem (Op8XY0 vx vy) = setRgst vx =<< getRgst vy
opCodeSem (Op8XY1 vx vy) = setRgst vx =<< (.|.)   <$> getRgst vx <*> getRgst vy
opCodeSem (Op8XY2 vx vy) = setRgst vx =<< (.&.)   <$> getRgst vx <*> getRgst vy
opCodeSem (Op8XY3 vx vy) = setRgst vx =<<  xor    <$> getRgst vx <*> getRgst vy
opCodeSem (Op8XY4 vx vy) = opRgstsWithFlag DW8.addWithCarry       vx vx vy
opCodeSem (Op8XY5 vx vy) = opRgstsWithFlag DW8.subWithBorrow      vx vx vy
opCodeSem (Op8XY6 vx)    = opRgstsWithFlag (const DW8.shiftRight) vx vx vx
opCodeSem (Op8XY7 vx vy) = opRgstsWithFlag (fmap (fmap not) . DW8.subWithBorrow) vx vy vx
opCodeSem (Op8XYE vx)    = opRgstsWithFlag (const DW8.shiftLeft)  vx vx vx
opCodeSem (Op9XY0 vx vy) = skipNextIf =<< (/=)    <$> getRgst vx <*> getRgst vy
opCodeSem (OpANNN add)   = setI add
opCodeSem (OpBNNN add)   = jmpTo . (add +) . fromIntegral =<< getRgst 0
opCodeSem (OpCXNN vx nn) = setRgst vx =<< (nn +) <$> getRandom
opCodeSem (OpEX9E vx)    = skipNextIf       =<< (flip (!) . fromIntegral) <$> getRgst vx <*> CMS.gets keys
opCodeSem (OpEXA1 vx)    = skipNextIf . not =<< (flip (!) . fromIntegral) <$> getRgst vx <*> CMS.gets keys
opCodeSem (OpFX07 vx)    = setRgst vx =<< CMS.gets delay
opCodeSem (OpFX15 vx)    = setDelay =<< getRgst vx
opCodeSem (OpFX18 vx)    = setSound =<< getRgst vx
opCodeSem (OpFX1E vx)    = incrIByRgstWithFlag vx
opCodeSem (OpFX55 vx)    = writeToMem vx
opCodeSem (OpFX65 vx)    = readFromMem vx
