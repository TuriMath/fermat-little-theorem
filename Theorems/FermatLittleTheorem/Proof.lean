import Theorems.FermatLittleTheorem.A
import Mathlib

namespace TuriMath.FermatLittleTheorem

/-- Binomial step: `(n+1)^p ≡ n^p + 1 (mod p)` for prime `p`. -/
private lemma step (p : ℕ) (hp : p.Prime) (n : ℤ) :
    (p : ℤ) ∣ (n + 1) ^ p - (n ^ p + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [one_pow, mul_one, Nat.choose_self, Nat.choose_zero_right, Nat.sub_self,
    Nat.cast_one, pow_zero, Nat.sub_zero]
  have : (↑(q + 1) : ℤ) ∣ ∑ k ∈ Finset.range q, n ^ (k + 1) * ↑((q + 1).choose (k + 1)) := by
    apply Finset.dvd_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    apply Dvd.dvd.mul_left
    exact_mod_cast hp.dvd_choose_self (by omega) (by omega)
  have e : ∑ k ∈ Finset.range q, n ^ (k + 1) * ↑((q + 1).choose (k + 1)) + 1 + n ^ (q + 1)
      - (n ^ (q + 1) + 1) = ∑ k ∈ Finset.range q, n ^ (k + 1) * ↑((q + 1).choose (k + 1)) := by
    ring
  rw [e]; exact this

private lemma nat_case (p : ℕ) (hp : p.Prime) (n : ℕ) : (p : ℤ) ∣ (n : ℤ) ^ p - n := by
  induction n with
  | zero => simp [hp.ne_zero]
  | succ k ih =>
    have := dvd_add (step p hp k) ih
    push_cast
    convert this using 1; ring

/-- Fermat's little theorem, from the binomial theorem and induction (no `ZMod.pow_card`). -/
theorem main : A.Statement := by
  intro p hp a
  rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
  · exact nat_case p hp n
  · rcases hp.eq_two_or_odd' with rfl | hodd
    · have h2 := nat_case 2 Nat.prime_two n
      have : (-(n:ℤ)) ^ 2 - -(n:ℤ) = ((n:ℤ) ^ 2 - n) + 2 * n := by ring
      rw [this]; exact dvd_add h2 (by push_cast; exact dvd_mul_right _ _)
    · have := nat_case p hp n
      rw [hodd.neg_pow]
      have e : -(n:ℤ) ^ p - -(n:ℤ) = -((n:ℤ) ^ p - n) := by ring
      rw [e]; exact (dvd_neg).2 this

end TuriMath.FermatLittleTheorem
