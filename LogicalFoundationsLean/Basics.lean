-- # Basics
-- Website: https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html

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
namespace MyBool -- to shadow original Bool

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

end MyBool

-- ### Types
