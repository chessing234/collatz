import Collatz.Accelerated

namespace Collatz.FirstLightDescent

def FirstLight (n k : Nat) : Prop :=
  3^oddCount n k < 2^k ∧ ∀ i, i<k → 2^i ≤ 3^oddCount n i

instance (n k : Nat) : Decidable (FirstLight n k) :=
  inferInstanceAs (Decidable (_ ∧ ∀ i, i<k → _))

/-- Any light prefix has a least light prefix no later than itself. -/
theorem least_light_prefix (n k : Nat) (hl : 3^oddCount n k < 2^k) :
    ∃ j, j≤k ∧ FirstLight n j := by
  classical
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hex : ∃ j, j<k ∧ 3^oddCount n j < 2^j
    · obtain ⟨j, hj, hlight⟩ := hex
      obtain ⟨i, hi, hf⟩ := ih j hj hlight
      exact ⟨i, by omega, hf⟩
    · refine ⟨k, Nat.le_refl k, hl, ?_⟩
      intro j hj
      have hnot : ¬ 3^oddCount n j < 2^j := fun h => hex ⟨j, hj, h⟩
      omega

end Collatz.FirstLightDescent
