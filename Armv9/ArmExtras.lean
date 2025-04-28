
import Armv9.Sail.Sail
import Armv9.Defs

open Sail

abbrev sign_extend {w : Nat} (x : BitVec w) (w' : Nat) := Sail.BitVec.signExtend x w'

def dec_str (x : Int) := x.repr
def hex_str (x : Int) := x.toHex

def putchar (_ : Int) : Unit := ()
