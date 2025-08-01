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

-- ### Numbers
namespace NatPlayground

inductive nat : Type where
  | O
  | S (n : nat)
deriving Repr, DecidableEq

def pred (n: nat) : nat :=
  match n with
    | .O => .O
    | .S n' => n'

end NatPlayground

#eval Nat.succ (.succ (.succ (.succ .zero)))

-- Coq style
def minustwo (n: Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ .zero => .zero
  | .succ (.succ n') => n'

-- Lean version - more concise
def minustwo' (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | n' + 2 => n'

#eval minustwo 4
#eval minustwo' 4

def even (n: Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => false
  | n' + 2 => even n'

def odd (n: Nat) : Bool :=
  Bool.not (even n)

example : odd 1 = true := by rfl
example : odd 4 = false := by rfl

def plus (n: Nat) (m: Nat) : Nat :=
  match n with
  | 0 => m
  | n' + 1 => (plus n' m) + 1

#eval plus 2 3

def mult (n m: Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => m
  | n' + 1 => plus m (mult n' m)

example : mult 3 3 = 9 := by rfl
example : mult 2 4 = 8 := by rfl

def minus (n m: Nat) : Nat :=
  match n, m with
  | 0, _ => 0
  | _ + 1, 0 => n
  | n' + 1, m' + 1 => minus n' m'

example : minus 4 2 = 2 := by rfl
example : minus 7 3 = 4 := by rfl

def exp (base power: Nat) : Nat :=
  match power with
  | 0 => 1
  | n' + 1 => mult base (exp base n')

example : exp 2 4 = 16 := by rfl

def factorial (n: Nat) : Nat :=
  match n with
  | 0 => 1
  | n' + 1 => mult n (factorial n')

example : factorial 3 = 6 := by rfl
example : factorial 5 = mult 10 12 := by rfl

def eqb (n m : Nat) : Bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | _ + 1 => false
  | n' + 1 => match m with
            | 0 => false
            | m' + 1 => eqb n' m'

example : eqb 2 2 = true := by rfl
example : eqb 2 3 = false := by rfl

def leb (n m : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 =>
    match m with
    | 0 => false
    | m' + 1 => leb n' m'

example : leb 2 2 = true := by rfl
example : leb 2 4 = true := by rfl
example : leb 4 2 = false := by rfl

notation:70 x " =? " y => eqb x y
notation:70 x " <=? " y => leb x y

def ltb (n m: Nat) : Bool :=
  leb (n + 1) m

example : ltb 2 2 = false := by rfl
example : ltb 2 4 = true := by rfl
example : ltb 3 4 = true := by rfl
example : ltb 4 2 = false := by rfl

-- ## Proof by Simplification

theorem plus_O_n : ∀ n: Nat, 0 + n = n := by simp

-- skip plus_O_n' because 'simp' already solves the goal

theorem plus_O_n'' : ∀ n : Nat, 0 + n = n := by
  intro m
  simp

theorem plus_1_l : ∀ n : Nat, 1 + n = n.succ := by
  apply Nat.add_comm -- no idea how to solve it without tactic used later, rfl and simp don't work

theorem mult_0_l : ∀ n : Nat, 0 * n = 0 := by
  intro n
  simp

-- ## Proof by Rewriting

theorem plus_id_example (n m : Nat) (h : n = m) : n + n = m + m := by
  rw [h]

theorem plus_id_exercise (n m o : Nat) (h1: n = m)  (h2: m = o) : n + m = m + o := by
  rw [h1]
  rw [h2]

#check Nat.mul_zero -- mult_n_O from Coq
#check Nat.mul_add_one -- mult_n_Sm from Coq

theorem mult_n_0_m_0 (p q : Nat) : (p * 0) + (q * 0) = 0 := by
  intros
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]

theorem mult_n_1 (p : Nat) : p * 1 = p := by
  intros
  rw [Nat.mul_add_one]
  rw [Nat.mul_zero]
  rw [Nat.zero_add] -- or rw [plus_O_n]

-- ## Proof by Case Analysis

theorem plus_1_neq_0 (n : Nat) :
  ((n + 1) =? 0) = false := by
  cases n with
  | zero => rfl
  | succ n' => rfl

namespace MyBool
-- I want to recreate boolean definitions and theorems from scratch
-- similar as much as possible to these from the book
-- if you want use Lean counterparts you can replace
-- negb, andb, orb, etc. with not, and, or and other defs
-- from the standard library

theorem negb_involutive (b : Bool) : negb (negb b) = b := by
  cases b with
  | true => rfl
  | false => rfl

theorem andb_commutative (b c : Bool) : andb b c = andb c b := by
  intros
  cases b with
  | true => cases c with
    | true => rfl
    | false => rfl
  | false => cases c with
    | true => rfl
    | false => rfl

end MyBool

-- examples without my own Bool type

theorem not_involutive (b : Bool) : not (not b) = b := by
  cases b with
  | true => rfl
  | false => rfl

theorem and_commutative (b c : Bool) : and b c = and c b := by
  intros
  cases b with
  | true => cases c with
    | true => rfl
    | false => rfl
  | false => cases c with
    | true => rfl
    | false => rfl

namespace MyBool

theorem andb3_exchange (b c d: Bool) : andb (andb b c) d = andb (andb b d) c := by
  intros
  cases b with
  | true => cases c with
    | true => cases d with
      | true => rfl
      | false => rfl
    | false => cases d with
      | true => rfl
      | false => rfl
  | false => cases c with
    | true => cases d with
      | true => rfl
      | false => rfl
    | false => cases d with
      | true => rfl
      | false => rfl

theorem andb_true_elim2 (b c : Bool) (h : andb b c = .true) : c = .true := by
  cases c with
    | true =>
      rfl
    | false =>
      -- goal: andb b false = true -> false = true
      rw [<-h]
      cases b with
      | true =>
        rfl
      | false =>
        rfl

theorem plus_1_neq_0' (n : Nat) : ((n + 1) =? 0) = false := by
  cases n with
  | zero => rfl
  | succ => rfl

theorem andb_commutative''
  (b c: Bool) : andb b c = andb c b := by
  cases b <;> cases c <;> rfl -- cases b <;> is same as intros [] [] in Coq

theorem zero_nbeq_plus_1 (n : Nat) :
  (0 =? (n + 1)) = false := by
  cases n with
  | zero => rfl
  | succ => rfl

end MyBool

-- ### Fixpoints and Structural Recursion (Optional)

-- No idea how to do it, ChatGPT says that the equivalent of this code below
-- would not be accepted in the Coq.
def safePred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => n

def trickyAdd (n m : Nat) : Nat :=
  match n with
  | 0 => m
  | n' + 1 => trickyAdd n' (safePred m)
