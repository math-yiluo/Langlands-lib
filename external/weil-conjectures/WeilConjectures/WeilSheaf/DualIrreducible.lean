/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.FiniteLength

/-!
# The dual of an irreducible lisse Weil sheaf

On a `k₀`-scheme with irreducible geometric fiber, the dual `M^∨` of an irreducible lisse Weil
sheaf `M` is irreducible lisse: a lisse subsheaf `N ⊆ M^∨` dualises to a lisse quotient
`M ≅ M^∨∨ ↠ N^∨`, whose kernel is a lisse subsheaf of `M`.

The dualised morphism `M ⟶ N^∨` is the transpose `m ↦ (n ↦ i(n)(m))` of the inclusion
`i : N ⟶ M^∨` (`AlgebraicGeometry.WeilSheaf.dualTranspose`), which is compatible with the Weil
structures since the evaluations `F^∨ ⊗ F ⟶ ℚ̄_ℓ` are. If it vanishes, so does `i`; otherwise
it is injective, `M` being irreducible, and comparing the ranks of the stalks shows that `i` is
an isomorphism.

## Main statements

- `AlgebraicGeometry.WeilSheaf.dualTranspose`: the transpose `M ⟶ N^∨` of a morphism
  `N ⟶ M^∨` of Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.finrankStalk_dual`: the dual of a lisse Weil sheaf has the same
  ranks.
- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.dual`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal AlgebraicGeometry.ProEtale

namespace CategoryTheory.Functor.LaxBraided

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  (G : C ⥤ C) [G.LaxBraided]

/-- An abstract form of the compatibility of a transpose with Weil structures. Let `G` be a lax
braided endofunctor, `evM : D ⊗ M ⟶ c` and `evN : E ⊗ N ⟶ c` "evaluations" compatible with
structure morphisms `φ : G _ ⟶ _` (with `ψN` a section of `φN`), and `T : M ⟶ E` the transpose of
`i : N ⟶ D` (`hT`). If `i` commutes with the structure morphisms, then so does `T`, after
evaluation. -/
lemma whiskerRight_evaluation_comm_of_transpose {M N D E c : C} {φM : G.obj M ⟶ M}
    {φN : G.obj N ⟶ N} {ψN : N ⟶ G.obj N} {φD : G.obj D ⟶ D} {φE : G.obj E ⟶ E}
    {φc : G.obj c ⟶ c} {evM : D ⊗ M ⟶ c} {evN : E ⊗ N ⟶ c} {i : N ⟶ D} {T : M ⟶ E}
    (hT : T ▷ N ≫ evN = (β_ M N).hom ≫ i ▷ M ≫ evM) (hi : G.map i ≫ φD = φN ≫ i)
    (hψ : ψN ≫ φN = 𝟙 N) (hD : (φD ⊗ₘ φM) ≫ evM = μ G D M ≫ G.map evM ≫ φc)
    (hE : φE ▷ N ≫ evN = G.obj E ◁ ψN ≫ μ G E N ≫ G.map evN ≫ φc) :
    (G.map T ≫ φE) ▷ N ≫ evN = (φM ≫ T) ▷ N ≫ evN := by
  have hi' : i = ψN ≫ G.map i ≫ φD := by rw [hi, reassoc_of% hψ]
  rw [comp_whiskerRight_assoc, hE, ← whisker_exchange_assoc, μ_natural_left_assoc,
    ← G.map_comp_assoc, hT, G.map_comp_assoc, braided_assoc,
    BraidedCategory.braiding_naturality_right_assoc, comp_whiskerRight_assoc, hT,
    BraidedCategory.braiding_naturality_left_assoc, whisker_exchange_assoc]
  conv_rhs => rw [hi']
  rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc, ← tensorHom_def_assoc, hD,
    μ_natural_left_assoc, G.map_comp_assoc]

end CategoryTheory.Functor.LaxBraided

namespace AlgebraicGeometry.WeilSheaf

section Transpose

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The evaluation `P^∨ ⊗ P ⟶ ℚ̄_ℓ` after the Weil structure of `P^∨`, in terms of the
Frobenius pullback of the evaluation (`AlgebraicGeometry.WeilSheaf.dual_evaluation_str`). -/
lemma dualStr_whiskerRight_evaluation (P : WeilSheaf k₀ l X) (hP : P.IsLisse) :
    (P.dual hP).obj.str.hom.hom ▷ P.obj.carrier.X ≫
        Mod.evaluation P.obj.carrier (adicConstant k₀ l X).obj.carrier =
      _ ◁ P.obj.str.inv.hom ≫
        μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
            WeilCoefficients.{u} l]
          (P.dual hP).obj.carrier.X P.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (Mod.evaluation P.obj.carrier (adicConstant k₀ l X).obj.carrier) ≫
        (adicConstant k₀ l X).obj.str.hom.hom := by
  have hφ : P.obj.str.inv.hom ≫ P.obj.str.hom.hom = 𝟙 _ :=
    congrArg Mod.Hom.hom P.obj.str.inv_hom_id
  rw [← dual_evaluation_str P hP, tensorHom_def', Category.assoc]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc, hφ]
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The transpose `M ⟶ N^∨`, `m ↦ (n ↦ i(n)(m))`, of a morphism `i : N ⟶ M^∨` of Weil sheaves,
`M` and `N` being lisse: the transpose `CategoryTheory.Mod.transpose` of the underlying
morphism of sheaves, which is compatible with the Weil structures since the evaluations
`M^∨ ⊗ M ⟶ ℚ̄_ℓ` and `N^∨ ⊗ N ⟶ ℚ̄_ℓ` are. -/
noncomputable def dualTranspose {M N : WeilSheaf k₀ l X} (hM : M.IsLisse) (hN : N.IsLisse)
    (i : N ⟶ M.dual hM) : M ⟶ N.dual hN :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ⟨Mod.transpose i.hom.hom.f, Mod.uncurryHom_injective
      (Functor.LaxBraided.whiskerRight_evaluation_comm_of_transpose
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
          WeilCoefficients.{u} l]
        (Mod.uncurryHom_transpose i.hom.hom.f) (congrArg Mod.Hom.hom i.hom.hom.h)
        (congrArg Mod.Hom.hom N.obj.str.inv_hom_id) (dual_evaluation_str M hM)
        (dualStr_whiskerRight_evaluation N hN))⟩)

lemma dualTranspose_hom_hom_f {M N : WeilSheaf k₀ l X} (hM : M.IsLisse) (hN : N.IsLisse)
    (i : N ⟶ M.dual hM) : (dualTranspose hM hN i).hom.hom.f = Mod.transpose i.hom.hom.f :=
  rfl

end Transpose

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

omit [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] in
/-- A subobject of a Weil sheaf has at most the same rank at every closed point. -/
theorem finrankStalk_le_of_mono {G F : WeilSheaf k₀ l X} (i : G ⟶ F) [Mono i]
    (x : X.finitePoints) : G.finrankStalk x ≤ F.finrankStalk x :=
  LinearMap.finrank_le_finrank_of_injective (injective_stalkAtMap _ _ _ i)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] in
/-- The dual of a lisse Weil sheaf has the same rank as the sheaf at every closed point. -/
theorem finrankStalk_dual {F : WeilSheaf k₀ l X} (hF : F.IsLisse) (x : X.finitePoints) :
    (F.dual hF).finrankStalk x = F.finrankStalk x := by
  obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF x
  exact e.toLinearEquiv.finrank_eq.trans Subspace.dual_finrank_eq

/-- The dual of an irreducible lisse Weil sheaf is irreducible lisse: for a lisse subsheaf
`i : N ⟶ M^∨`, the transpose `M ⟶ N^∨` (`AlgebraicGeometry.WeilSheaf.dualTranspose`) is zero,
and then so is `i`, so that `N = 0`, or injective, `M` being irreducible. In the latter case
the ranks of the stalks at a closed point satisfy `rk M ≤ rk N^∨ = rk N ≤ rk M^∨ = rk M`, so the
lisse cokernel of `i` has a zero stalk, hence vanishes. -/
theorem IsIrreducibleLisse.dual {M : WeilSheaf k₀ l X} (hM : M.IsIrreducibleLisse) :
    (M.dual hM.1).IsIrreducibleLisse := by
  obtain ⟨hL, hM0, hirr⟩ := hM
  obtain ⟨x, hx⟩ := M.exists_nontrivial_stalk_of_not_isZero hM0
  have hrk : 0 < M.finrankStalk x := Module.finrank_pos
  refine ⟨hL.dual, fun h ↦ ?_, fun N i hi hN ↦ ?_⟩
  · have h1 : ¬ Nontrivial ((M.dual hL).stalk x).carrier :=
      Set.eq_empty_iff_forall_notMem.1 (support_eq_empty_of_isZero h) x
    rw [not_nontrivial_iff_subsingleton] at h1
    have h2 : (M.dual hL).finrankStalk x = 0 := Module.finrank_zero_of_subsingleton
    rw [finrankStalk_dual] at h2
    omega
  by_cases hT : dualTranspose hL hN i = 0
  · left
    have h1 : Mod.transpose i.hom.hom.f = 0 := congrArg (fun f ↦ f.hom.hom.f) hT
    obtain rfl : i = 0 := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
      (Endofunctor.Algebra.Hom.ext ((Mod.transpose_eq_zero_iff _).1 h1)))
    exact IsZero.of_mono_zero N (M.dual hL)
  right
  have hTm : Mono (dualTranspose hL hN i) := by
    rcases hirr _ (kernel.ι (dualTranspose hL hN i)) inferInstance
        (hL.kernel hN.dual (dualTranspose hL hN i)) with hK | hK
    · exact Preadditive.mono_of_kernel_zero (hK.eq_of_src _ _)
    · exact absurd (by rw [← cancel_epi (kernel.ι (dualTranspose hL hN i)), kernel.condition,
        comp_zero]) hT
  have h1 := finrankStalk_le_of_mono (dualTranspose hL hN i) x
  have h2 := finrankStalk_le_of_mono i x
  rw [finrankStalk_dual] at h1 h2
  have hQ : IsZero (cokernel i) := by
    by_contra hQ
    have h3 := finrankStalk_lt_of_mono i x ((hN.cokernel hL.dual i).nontrivial_stalk hQ x)
    rw [finrankStalk_dual] at h3
    omega
  have : Epi i := Preadditive.epi_of_cokernel_zero (hQ.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi i

end AlgebraicGeometry.WeilSheaf
