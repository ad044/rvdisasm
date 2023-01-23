module Main where

import Control.Monad (unless)
import Data.Bits (Bits (shiftL, shiftR, xor, (.&.), (.|.)))
import Data.Char (isSpace)
import Data.Word (Word32)
import Math.NumberTheory.Logarithms (integerLog2)
import Text.Printf (printf)

data BitField = BitField
  { bits :: Word32,
    len :: Int
  }

bitLength :: Integral a => a -> Int
bitLength n = integerLog2 (fromIntegral n)

word32ToInt :: Word32 -> Int
word32ToInt = fromIntegral

twosComplement :: Word32 -> Word32 -> Int
twosComplement num mask =
  let negative = negate (word32ToInt (num `xor` mask + 1))
      bitLen = bitLength mask
      signBit = 32 - bitLen
   in if extractBits num (signBit - 1) signBit == 1 then negative else word32ToInt num

getRegisterAbiName :: Word32 -> String
getRegisterAbiName reg =
  case reg of
    0 -> "zero" -- hardwired zero
    1 -> "ra" -- return address
    2 -> "sp" -- stack pointer
    3 -> "gp" -- global pointer
    4 -> "tp" -- thread pointer
    5 -> "t0" -- temp register 0
    6 -> "t1" -- temp register 1
    7 -> "t2" -- temp register 2
    8 -> "s0 / fp" -- saved register 0 / frame pointer
    9 -> "s1" -- saved register 1
    10 -> "a0" -- function argument 0 / return value 0
    11 -> "a1" -- function argument 1 / return value 1
    12 -> "a2" -- function argument 2
    13 -> "a3" -- function argument 3
    14 -> "a4" -- function argument 4
    15 -> "a5" -- function argument 5
    16 -> "a6" -- function argument 6
    17 -> "a7" -- function argument 7
    18 -> "s2" -- saved register 2
    19 -> "s3" -- saved register 3
    20 -> "s4" -- saved register 4
    21 -> "s5" -- saved register 5
    22 -> "s6" -- saved register 6
    23 -> "s7" -- saved register 7
    24 -> "s8" -- saved register 8
    25 -> "s9" -- saved register 9
    26 -> "s10" -- saved register 10
    27 -> "s11" -- saved register 11
    28 -> "t3" -- temp register 3
    29 -> "t4" -- temp register 4
    30 -> "t5" -- temp register 5
    31 -> "t6" -- temp register 6
    _ -> "?"

-- Could have it output "0x%x" in case of positive values but it's easier to debug this way
formatImm :: Int -> String
formatImm = printf "%d"

concatBitFields :: BitField -> BitField -> BitField
concatBitFields a b =
  BitField {bits = (bits a `shiftL` len b) .|. bits b, len = len a + len b}

lastNBits :: Word32 -> Int -> Word32
lastNBits num n =
  let mask = (1 `shiftL` n) - 1
   in num .&. mask

extractBitsAsBitField :: Word32 -> Int -> Int -> BitField
extractBitsAsBitField num start end =
  let fieldSize = end - start
      bits = extractBits num start end
   in BitField {bits = bits, len = fieldSize}

extractBits :: Word32 -> Int -> Int -> Word32
extractBits num start end =
  let fieldSize = end - start
      shamt = 32 - end
   in lastNBits (num `shiftR` shamt) fieldSize

extractFunct3 :: Word32 -> Word32
extractFunct3 op = extractBits op 17 20

extractFunct7 :: Word32 -> Word32
extractFunct7 op = extractBits op 0 7

extractRs1 :: Word32 -> Word32
extractRs1 op = extractBits op 12 17

extractRs2 :: Word32 -> Word32
extractRs2 op = extractBits op 7 12

extractRd :: Word32 -> Word32
extractRd op = extractBits op 20 25

extractOpcode :: Word32 -> Word32
extractOpcode op = extractBits op 25 32

-- R-Format
formatR :: String -> Word32 -> Word32 -> Word32 -> String
formatR mnemonic rd rs1 rs2 =
  printf
    "%s %s, %s, %s"
    mnemonic
    (getRegisterAbiName rd)
    (getRegisterAbiName rs1)
    (getRegisterAbiName rs2)

getMnemonicR :: Word32 -> Word32 -> Word32 -> String
getMnemonicR opcode funct3 funct7 =
  case (opcode, funct3, funct7) of
    (0x33, 0x0, 0x0) -> "add"
    (0x33, 0x0, 0x20) -> "sub"
    (0x33, 0x1, 0x0) -> "sll"
    (0x33, 0x2, 0x0) -> "slt"
    (0x33, 0x3, 0x0) -> "sltu"
    (0x33, 0x4, 0x0) -> "xor"
    (0x33, 0x5, 0x0) -> "srl"
    (0x33, 0x5, 0x20) -> "sra"
    (0x33, 0x6, 0x0) -> "or"
    (0x33, 0x7, 0x0) -> "and"
    (0x3b, 0x0, 0x0) -> "addw"
    (0x3b, 0x1, 0x0) -> "sllw"
    (0x3b, 0x5, 0x20) -> "sraw"
    (0x3b, 0x5, 0x0) -> "srlw"
    (0x3b, 0x0, 0x20) -> "subw"
    _ -> "?"

decodeR :: Word32 -> String
decodeR op =
  let opcode = extractOpcode op
      rd = extractRd op
      rs1 = extractRs1 op
      rs2 = extractRs2 op
      funct3 = extractFunct3 op
      funct7 = extractFunct7 op
      mnemonic = getMnemonicR opcode funct3 funct7
   in formatR mnemonic rd rs1 rs2

-- I-Format
formatI :: String -> Word32 -> Word32 -> Int -> String
formatI mnemonic rd rs imm =
  printf
    "%s %s, %s, %s"
    mnemonic
    (getRegisterAbiName rd)
    (getRegisterAbiName rs)
    (formatImm imm)

getMnemonicI :: Word32 -> Word32 -> Word32 -> String
getMnemonicI opcode funct3 immlo5 =
  case (opcode, funct3, immlo5) of
    (0x13, 0x0, _) -> "addi"
    (0x13, 0x7, _) -> "andi"
    (0x13, 0x6, _) -> "ori"
    (0x13, 0x2, _) -> "slti"
    (0x13, 0x3, _) -> "sltiu"
    (0x13, 0x4, _) -> "xori"
    (0x13, 0x5, 0x10) -> "srai"
    (0x13, 0x5, 0x0) -> "srli"
    (0x13, 0x1, 0x0) -> "slli"
    (0x3, 0x0, _) -> "lb"
    (0x3, 0x4, _) -> "lbu"
    (0x3, 0x3, _) -> "ld"
    (0x3, 0x1, _) -> "lh"
    (0x3, 0x5, _) -> "lhu"
    (0x3, 0x2, _) -> "lw"
    (0x3, 0x6, _) -> "lwu"
    (0x67, 0x0, _) -> "jalr"
    (0x1b, 0x1, 0x0) -> "slliw"
    (0x1b, 0x0, _) -> "addiw"
    (0x1b, 0x5, 0x10) -> "sraiw"
    (0x1b, 0x5, 0x0) -> "srliw"
    _ -> "?"

decodeI :: Word32 -> String
decodeI op =
  let opcode = extractOpcode op
      rd = extractRd op
      rs1 = extractRs1 op
      funct3 = extractFunct3 op
      imm12 = extractBits op 0 12
      immlo5 = extractBits imm12 6 13
      simm12 = twosComplement imm12 0xFFF
      mnemonic = getMnemonicI opcode funct3 immlo5
   in if mnemonic `elem` ["slli", "slliw", "srai", "sraiw", "srli", "srliw"]
        then formatI mnemonic rd rs1 (word32ToInt immlo5)
        else formatI mnemonic rd rs1 simm12

-- S-Format
formatS :: String -> Word32 -> Word32 -> Word32 -> String
formatS mnemonic rs1 rs2 imm =
  printf
    "%s %s, %d(%s)"
    mnemonic
    (getRegisterAbiName rs2)
    imm
    (getRegisterAbiName rs1)

getMnemonicS :: Word32 -> String
getMnemonicS funct3 =
  case funct3 of
    0x0 -> "sb"
    0x1 -> "sh"
    0x2 -> "sw"
    0x3 -> "sd"
    _ -> "?"

decodeS :: Word32 -> String
decodeS op =
  let rs1 = extractRs1 op
      rs2 = extractRs2 op
      funct3 = extractFunct3 op
      immhi7 = extractBitsAsBitField op 0 7
      immlo5 = extractBitsAsBitField op 20 25
      imm12 = concatBitFields immhi7 immlo5
      mnemonic = getMnemonicS funct3
   in formatS mnemonic rs1 rs2 (bits imm12)

-- B-Format
formatB :: String -> Word32 -> Word32 -> Int -> String
formatB mnemonic rs1 rs2 imm =
  printf
    "%s %s, %s, %s"
    mnemonic
    (getRegisterAbiName rs1)
    (getRegisterAbiName rs2)
    (formatImm imm)

getMnemonicB :: Word32 -> String
getMnemonicB funct3 =
  case funct3 of
    0x0 -> "beq"
    0x1 -> "bne"
    0x4 -> "blt"
    0x5 -> "bge"
    0x6 -> "bltu"
    0x7 -> "bgeu"
    _ -> "?"

decodeB :: Word32 -> String
decodeB op =
  let rs1 = extractRs1 op
      rs2 = extractRs2 op
      funct3 = extractFunct3 op
      mnemonic = getMnemonicB funct3
      imm =
        foldl
          concatBitFields
          BitField {bits = 0, len = 0}
          [ extractBitsAsBitField op 0 1,
            extractBitsAsBitField op 24 25,
            extractBitsAsBitField op 1 7,
            extractBitsAsBitField op 20 24
          ]
      simm = twosComplement (bits imm `shiftL` 1) 0x1FFF
   in formatB mnemonic rs1 rs2 simm

-- U-Format
formatU :: String -> Word32 -> Int -> String
formatU mnemonic rd imm =
  printf "%s, %s, %s" mnemonic (getRegisterAbiName rd) (formatImm imm)

getMnemonicU :: Word32 -> String
getMnemonicU opcode =
  case opcode of
    0x37 -> "lui"
    0x17 -> "auipc"
    _ -> "?"

decodeU :: Word32 -> String
decodeU op =
  let opcode = extractOpcode op
      rd = extractRd op
      simm = twosComplement (extractBits op 0 20) 0xFFFFF
      mnemonic = getMnemonicU opcode
   in formatU mnemonic rd simm

-- J-Format
formatJ :: String -> Word32 -> Int -> String
formatJ mnemonic rd imm =
  printf "%s %s, %s" mnemonic (getRegisterAbiName rd) (formatImm imm)

getMnemonicJ :: Word32 -> String
getMnemonicJ opcode =
  case opcode of
    0x6F -> "jal"
    _ -> "?"

decodeJ :: Word32 -> String
decodeJ op =
  let opcode = extractOpcode op
      rd = extractRd op
      mnemonic = getMnemonicJ opcode
      imm =
        foldl
          concatBitFields
          BitField {bits = 0, len = 0}
          [ extractBitsAsBitField op 0 1,
            extractBitsAsBitField op 12 20,
            extractBitsAsBitField op 11 12,
            extractBitsAsBitField op 1 11
          ]

      simm = twosComplement (bits imm) 0xFFFFF
   in formatJ mnemonic rd (simm `shiftL` 1)

-- Main decoder function
decode :: Word32 -> String
decode op =
  case op of
    0x100073 -> "ebreak"
    0x73 -> "ecall"
    _ ->
      case extractOpcode op of
        0x33 -> decodeR op
        0x2F -> decodeR op
        0x1b -> decodeI op
        0x3 -> decodeI op
        0x67 -> decodeI op
        0x13 -> decodeI op
        0x23 -> decodeS op
        0x63 -> decodeB op
        0x17 -> decodeU op
        0x37 -> decodeU op
        0x6F -> decodeJ op
        _ -> "UNKNOWN OP"

-- Utils
hexChar :: Char -> Maybe Word32
hexChar ch
  | ch == '0' = Just 0
  | ch == '1' = Just 1
  | ch == '2' = Just 2
  | ch == '3' = Just 3
  | ch == '4' = Just 4
  | ch == '5' = Just 5
  | ch == '6' = Just 6
  | ch == '7' = Just 7
  | ch == '8' = Just 8
  | ch == '9' = Just 9
  | ch == 'A' = Just 10
  | ch == 'B' = Just 11
  | ch == 'C' = Just 12
  | ch == 'D' = Just 13
  | ch == 'E' = Just 14
  | ch == 'F' = Just 15
  | ch == 'a' = Just 10
  | ch == 'b' = Just 11
  | ch == 'c' = Just 12
  | ch == 'd' = Just 13
  | ch == 'e' = Just 14
  | ch == 'f' = Just 15
  | otherwise = Nothing

parseHex :: String -> Word32
parseHex [] = 0
parseHex hxStr = case hexChar (last hxStr) of
  Just value -> value + 16 * parseHex (init hxStr)
  Nothing -> error "Failed to parse hex string"

decodeLine :: String -> String
decodeLine line =
  let op = parseHex line
   in decode op

splitIntoChunksOfLength :: Int -> String -> [String]
splitIntoChunksOfLength n [] = []
splitIntoChunksOfLength n xs = take n xs : splitIntoChunksOfLength n (drop n xs)

-- Entrypoint
main :: IO ()
main = do
  line <- getLine
  unless (line == "exit") $ do
    let cleanLine = filter (not . isSpace) line
        instructions = splitIntoChunksOfLength 8 cleanLine
        decoded = map decodeLine instructions
     in mapM_ putStrLn decoded
    main
