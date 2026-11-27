import RequestProject.Main1

/- The measure bound is due to Franchi, Gowers and Yip, formalized with
   Aristotle (Harmonic). This file derives the LeftToSolve formulation. -/
open Set MeasureTheory

theorem OMA.solution :
    ∀ A : Set ℝ, IsOpen A → A ⊆ Icc 0 1 → volume A > 1 / 3 →
      ∃ x y z, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ x * y = z := by
  classical
  intro A hopen hsub hvol
  by_contra h
  have hin : A ⊆ Ioo (0 : ℝ) 1 := by
    rw [← interior_Icc]
    exact hopen.subset_interior_iff.mpr hsub
  have hpf : ProductFree.IsProductFree A :=
    fun hx hy hxy => h ⟨_, _, _, hx, hy, hxy, rfl⟩
  have hbound := ProductFree.main1 hopen hin hpf
  rw [ENNReal.ofReal_div_of_pos (by norm_num)] at hbound
  exact (not_le.mpr hvol) (by simpa only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hbound)

#print axioms OMA.solution
