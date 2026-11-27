import Mathlib

/-!
# Fermat's little theorem — statement A (Noether)

Source (Wikipedia, "Fermat's little theorem", lead; Hardy & Wright Thm 70/71):
> if p is a prime number, then for any integer a, the number a^p − a is an integer
> multiple of p. In the notation of modular arithmetic, this is expressed as a^p ≡ a (mod p).
-/

namespace TuriMath.FermatLittleTheorem.A

/-- Fermat's little theorem, `a ^ p ≡ a (mod p)` form, for every integer `a`.

Mapping, source → Lean:
* "p is a prime number"          → `p : ℕ` with `p.Prime` (Mathlib's `Nat.Prime`; ℕ because a
                                    prime number is a natural number, per the issue note).
* "for any integer a"            → `∀ a : ℤ`, no further hypothesis (negative `a` and multiples
                                    of `p` included; no `p ∤ a`).
* "the number a^p − a"           → `a ^ p - a`, computed in ℤ (`a ^ p` is `Monoid.npow`, exponent `p : ℕ`).
* "is an integer multiple of p"  → `(p : ℤ) ∣ a ^ p - a` (Mathlib `Dvd` on ℤ: `∃ k : ℤ, a ^ p - a = p * k`).
* "a^p ≡ a (mod p)"              → the same claim: `p ∣ a ^ p - a ↔ a ≡ a ^ p [ZMOD p]`
                                    (`Int.modEq_of_dvd` / `Int.ModEq.dvd`), and `Int.ModEq` is
                                    symmetric, so the divisibility form covers both sentences.
-/
def Statement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ a : ℤ, (p : ℤ) ∣ a ^ p - a

/-! ## Sanity section

The only hypothesis is `p.Prime` (plus `a : ℤ`, which is unconstrained).
Below: it can hold, with a concrete `a`. -/

example : ∃ p : ℕ, p.Prime ∧ ∃ _a : ℤ, True := ⟨2, Nat.prime_two, -3, trivial⟩

end TuriMath.FermatLittleTheorem.A
