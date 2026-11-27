import Mathlib

/-!
# Fermat's little theorem — statement B (Gauss, blind to A)

Source (Wikipedia, "Fermat's little theorem", lead; Hardy & Wright Thm 70/71):
> In number theory, Fermat's little theorem states that if p is a prime number, then for any
> integer a, the number a^p − a is an integer multiple of p. In the notation of modular
> arithmetic, this is expressed as a^p ≡ a (mod p).

Mapping, one line per part of the quote:
* "p is a prime number"            ↦ `p : ℕ` with `Nat.Prime p` (a natural-number prime).
* "for any integer a"              ↦ `∀ a : ℤ` (no restriction: negatives and multiples of p included).
* "the number a^p − a"             ↦ `a ^ p - a`, computed in `ℤ`.
* "is an integer multiple of p"    ↦ `(p : ℤ) ∣ a ^ p - a`, i.e. `∃ k : ℤ, a ^ p - a = p * k`.
* "a^p ≡ a (mod p)"                ↦ the same fact; we use the elementary divisibility phrasing
                                      (the first sentence) rather than `Int.ModEq` or `ZMod`.
-/

namespace TuriMath.FermatLittleTheorem.B

/-- For every natural prime `p` and every integer `a`, `p` divides `a ^ p - a` in `ℤ`. -/
def Statement : Prop :=
  ∀ p : ℕ, Nat.Prime p → ∀ a : ℤ, (p : ℤ) ∣ a ^ p - a

/-! ## Sanity section: the hypotheses can all hold at once -/

/-- There is a prime `p` and an integer `a` (indeed `p = 2`, `a = 3`). -/
example : ∃ p : ℕ, Nat.Prime p ∧ ∃ _a : ℤ, True := ⟨2, Nat.prime_two, 3, trivial⟩

/-- The hypotheses also hold with a negative `a` and with `a` a multiple of `p`. -/
example : Nat.Prime 5 ∧ (-3 : ℤ) < 0 ∧ (5 : ℤ) ∣ 10 := ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## Concrete checks of the conclusion on small cases -/

/-- p = 5, a = 2: 2^5 − 2 = 30 = 5 · 6. -/
example : ((5 : ℕ) : ℤ) ∣ (2 : ℤ) ^ 5 - 2 := ⟨6, by norm_num⟩

/-- p = 3, a = −4 (negative a): (−4)^3 − (−4) = −64 + 4 = −60 = 3 · (−20). -/
example : ((3 : ℕ) : ℤ) ∣ (-4 : ℤ) ^ 3 - (-4) := ⟨-20, by norm_num⟩

/-- p = 7, a = 14 (a multiple of p): 14^7 − 14 is divisible by 7. -/
example : ((7 : ℕ) : ℤ) ∣ (14 : ℤ) ^ 7 - 14 := by decide

/-- p = 2, a = 0 and a = 1: 0 − 0 = 0 and 1 − 1 = 0, both divisible by 2. -/
example : ((2 : ℕ) : ℤ) ∣ (0 : ℤ) ^ 2 - 0 ∧ ((2 : ℕ) : ℤ) ∣ (1 : ℤ) ^ 2 - 1 := by decide

/-- The prime hypothesis matters: for p = 4 (not prime), a = 2 gives 2^4 − 2 = 14, not divisible
by 4. So the statement is not trivially true for all `p`. -/
example : ¬ ((4 : ℕ) : ℤ) ∣ (2 : ℤ) ^ 4 - 2 := by decide

end TuriMath.FermatLittleTheorem.B
