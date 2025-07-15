-- # Basics
-- Website: https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html

namespace MyBool -- to shadow original Bool

-- ## Data and Functions

-- ### Days of the Week

inductive Day where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr, DecidableEq

def nextWorkingDay (d: Day) : Day :=
  match d with
  | Day.monday => Day.tuesday
  | Day.tuesday => Day.wednesday
  | Day.wednesday => Day.thursday
  | Day.thursday => Day.friday
  | Day.friday => Day.monday
  | Day.saturday => Day.monday
  | Day.sunday => Day.monday

#eval nextWorkingDay Day.friday -- Evaluates to monday
#eval nextWorkingDay (nextWorkingDay Day.saturday) -- Evaluates to tuesday

example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by rfl

-- ### Booleans

inductive Bool : Type where
  | true
  | false
deriving Repr, DecidableEq

def negb (b: Bool) : Bool :=
  match b with
  | Bool.true => Bool.false
  | Bool.false => Bool.true

def andb (b1: Bool) (b2: Bool) : Bool :=
  match b1 with
  | Bool.true => b2
  | Bool.false => Bool.false

def orb (b1: Bool) (b2: Bool) : Bool :=
  match b1 with
  | Bool.true => Bool.true
  | Bool.false => b2

example : orb Bool.true Bool.false = Bool.true := by rfl
example : orb Bool.false Bool.false = Bool.false := by rfl
example : orb Bool.false Bool.true = Bool.true := by rfl
example : orb Bool.true Bool.true = Bool.true := by rfl

notation x " && " y => andb x y
notation x " || " y => orb x y

example : (Bool.true && Bool.false) = Bool.false := by rfl

def negb' (b: Bool) : Bool :=
  if b == Bool.true
    then Bool.false
    else Bool.true

def andb' (b1: Bool) (b2: Bool) : Bool :=
  if b1 == Bool.true
    then b2
    else Bool.false

def orb' (b1: Bool) (b2: Bool) : Bool :=
  if b1 == Bool.true
    then Bool.true
    else b2

-- another type example: bw type
inductive bw : Type where
  | bw_black
  | bw_white
deriving Repr, DecidableEq

def invert (x: bw) : bw :=
  if x == bw.bw_black
    then bw.bw_white
    else bw.bw_black

#eval invert bw.bw_black
#eval invert bw.bw_white

-- nandb
def nandb (b1: Bool) (b2: Bool) : Bool :=
  negb (andb b1 b2)

example : nandb Bool.true Bool.false = Bool.true := by rfl
example : nandb Bool.false Bool.false = Bool.true := by rfl
example : nandb Bool.false Bool.true = Bool.true := by rfl
example : nandb Bool.true Bool.true = Bool.false := by rfl

-- andb3
def andb3 (b1: Bool) (b2: Bool) (b3: Bool) : Bool :=
  andb b1 (andb b2 b3)

example : andb3 Bool.true Bool.true Bool.true = Bool.true := by rfl
example : andb3 Bool.false Bool.true Bool.true = Bool.false := by rfl
example : andb3 Bool.true Bool.false Bool.true = Bool.false := by rfl
example : andb3 Bool.true Bool.true Bool.false = Bool.false := by rfl

-- ### Types

#check true

#check (negb Bool.true)

#check negb

-- ### New types from old

inductive rgb : Type where
  | red
  | green
  | blue

inductive color : Type where
  | black
  | white
  | primary (p: rgb)

def monochrome (c: color) : Bool :=
  match c with
  | color.black => Bool.true
  | color.white => Bool.true
  | color.primary _ => Bool.false

def isRed (c: color) : Bool :=
  match c with
  | color.black => Bool.false
  | color.white => Bool.false
  | color.primary rgb.red => Bool.true
  | color.primary _ => Bool.false

-- ### Modules
namespace Playground
  def foo : rgb := rgb.blue
end Playground

def foo : Bool := Bool.true

#check Playground.foo
#check foo

end MyBool
-- ### Tuples
namespace TuplePlayground

inductive bit : Type where
  | b1
  | b0
deriving Repr, DecidableEq

inductive nybble : Type where
  | bits (bit0 bit1 bit2 bit3 : bit)
deriving Repr, DecidableEq

#check (nybble.bits .b1 .b0 .b1 .b0)

def all_zero (nb: nybble) : Bool :=
  match nb with
  | (nybble.bits .b0 .b0 .b0 .b0) => true
  | (nybble.bits _ _ _ _) => false

#eval all_zero (nybble.bits .b1 .b0 .b1 .b0) -- false
#eval all_zero (nybble.bits .b0 .b0 .b0 .b0) -- true

end TuplePlayground
