import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19230 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (7919 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.and, [4, 3]⟩, ⟨.or, [4, 3]⟩, ⟨.not, [9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩
  · decide +kernel
