/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComapQuotient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ProjectiveTensorUnitCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# The homology sequence of a reduction triangle

For a central element `z` of an abelian category `C` and a distinguished triangle
`K --z--> K ⟶ K₁ ⟶ K[1]` in `D(C)`, we record the exact sequences relating the action of `z` on
the cohomology objects of `K` to the cohomology objects of `K₁`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-! ### The homology sequence of a reduction triangle -/

namespace CategoryTheory.CatCenter

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] (z : CatCenter C)
  {K K₁ : DerivedCategory C} {g : K ⟶ K₁} {h : K₁ ⟶ K⟦(1 : ℤ)⟧}

omit [HasDerivedCategory C] in
/-- A central element `z` acts on the homology of a homological complex `K` through the degreewise
action `z.mapHomologicalComplex`, as `z` itself. -/
private lemma homologyMap_app {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c)
    (i : ι) :
    HomologicalComplex.homologyMap ((z.mapHomologicalComplex c).app K) i =
      z.app (K.homology i) := by
  have hc : HomologicalComplex.cyclesMap ((z.mapHomologicalComplex c).app K) i =
      z.app (K.cycles i) := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i,
      mapHomologicalComplex_app_f, z.naturality]
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, hc, z.naturality]

/-- The central element of `D(C)` induced by `z` acts on the cohomology objects as `z`. -/
private lemma homologyFunctor_map_app (n : ℤ) (K : DerivedCategory C) :
    (DerivedCategory.homologyFunctor C n).map (z.derivedCategory.app K) =
      z.app ((DerivedCategory.homologyFunctor C n).obj K) := by
  refine map_app_of_iso _ _ _ (DerivedCategory.Q.objObjPreimageIso K) ?_
  rw [derivedCategory_app_Q_obj, ← cancel_mono
    ((DerivedCategory.homologyFunctorFactors C n).hom.app (DerivedCategory.Q.objPreimage K)),
    DerivedCategory.homologyFunctorFactors_hom_naturality, homologyMap_app]
  exact z.naturality _

/-- In a distinguished triangle `K --z--> K --g--> K₁ ⟶ K[1]` whose first map is a central
element, the sequence `Hᵠ K --z--> Hᵠ K --g--> Hᵠ K₁` is exact. -/
lemma exact_app_homologyFunctor_map
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q : ℤ) :
    (ShortComplex.mk (z.app ((DerivedCategory.homologyFunctor C q).obj K))
      ((DerivedCategory.homologyFunctor C q).map g) (by
        have hw : z.derivedCategory.app K ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
        rw [← homologyFunctor_map_app, ← Functor.map_comp, hw, Functor.map_zero])).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₂ _ hT q)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using (homologyFunctor_map_app z q K).symm) (by simp)

/-- In a distinguished triangle `K --z--> K --g--> K₁ ⟶ K[1]` whose first map is a central
element, the sequence `Hᵠ⁰ K₁ --δ--> Hᵠ¹ K --z--> Hᵠ¹ K` is exact, where `q₀ + 1 = q₁`. -/
lemma exact_δ_app_homologyFunctor
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) :
    (ShortComplex.mk (DerivedCategory.HomologySequence.δ
        (Triangle.mk (z.derivedCategory.app K) g h) q₀ q₁ hq)
      (z.app ((DerivedCategory.homologyFunctor C q₁).obj K)) (by
        rw [← homologyFunctor_map_app]
        exact DerivedCategory.HomologySequence.δ_comp _ hT q₀ q₁ hq)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₁ _ hT q₀ q₁ hq)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using (homologyFunctor_map_app z q₁ K).symm)

/-- If `Hᵠ K₁ = 0`, the central element `z` acts surjectively on `Hᵠ K`. -/
lemma epi_app_homologyFunctor_obj_of_isZero
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor C q).obj K₁)) :
    Epi (z.app ((DerivedCategory.homologyFunctor C q).obj K)) :=
  (exact_app_homologyFunctor_map z hT q).epi_f (hq.eq_of_tgt _ _)

/-- If `Hᵠ⁰ K₁ = 0`, the central element `z` acts injectively on `Hᵠ¹ K`, where
`q₀ + 1 = q₁`. -/
lemma mono_app_homologyFunctor_obj_of_isZero
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) (h₀ : IsZero ((DerivedCategory.homologyFunctor C q₀).obj K₁)) :
    Mono (z.app ((DerivedCategory.homologyFunctor C q₁).obj K)) :=
  (exact_δ_app_homologyFunctor z hT q₀ q₁ hq).mono_g (h₀.eq_of_src _ _)

/-- The kernel of the action of `z` on `Hᵠ¹ K` is a quotient of `Hᵠ⁰ K₁`, where `q₀ + 1 = q₁`. -/
lemma exists_epi_kernel_app_homologyFunctor_obj
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) :
    ∃ f : (DerivedCategory.homologyFunctor C q₀).obj K₁ ⟶
      kernel (z.app ((DerivedCategory.homologyFunctor C q₁).obj K)), Epi f :=
  ⟨_, (exact_δ_app_homologyFunctor z hT q₀ q₁ hq).epi_kernelLift⟩

/-- If `Hᵠ¹ K = 0`, the cokernel of the action of `z` on `Hᵠ⁰ K` is `Hᵠ⁰ K₁`, where
`q₀ + 1 = q₁`. -/
lemma nonempty_cokernel_app_homologyFunctor_obj_iso
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) (h₁ : IsZero ((DerivedCategory.homologyFunctor C q₁).obj K)) :
    Nonempty (cokernel (z.app ((DerivedCategory.homologyFunctor C q₀).obj K)) ≅
      (DerivedCategory.homologyFunctor C q₀).obj K₁) := by
  have : Epi ((DerivedCategory.homologyFunctor C q₀).map g) :=
    (DerivedCategory.HomologySequence.exact₃ _ hT q₀ q₁ hq).epi_f (h₁.eq_of_tgt _ _)
  exact ⟨(colimit.isColimit _).coconePointUniqueUpToIso
    (exact_app_homologyFunctor_map z hT q₀).gIsCokernel⟩

end CategoryTheory.CatCenter
