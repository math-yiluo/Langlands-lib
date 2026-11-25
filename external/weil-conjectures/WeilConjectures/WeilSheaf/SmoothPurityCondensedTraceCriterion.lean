/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTraceCriterion
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedAdjunction
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree
public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperBoundedBelowCoproducts

/-!
# Testing a condensed Weil trace on its geometric carrier

Uniformly bounded below sums suffice for the free Weil resolution. The required
preservation theorem is already available for condensed direct images.
-/

@[expose] public section

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

/-- A universal trace can be tested after fully faithful comparison of both categories. -/
theorem isIso_homEquiv_of_fullyFaithful_trace
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {J : D ⥤ C} (adj : L ⊣ J)
    (E : C ⥤ C') (E' : D ⥤ D') [E.Full] [E.Faithful] [E'.Full] [E'.Faithful]
    (L' : C' ⥤ D') (c : L ⋙ E' ≅ E ⋙ L')
    {P : C} {T : D} (ε : L.obj P ⟶ T) (δ : L'.obj (E.obj P) ⟶ E'.obj T)
    (hε : E'.map ε = c.hom.app P ≫ δ)
    (h : ∀ K : C, Function.Bijective fun φ : E.obj K ⟶ E.obj P ↦ L'.map φ ≫ δ) :
    IsIso (adj.homEquiv P T ε) := by
  apply isIso_homEquiv_of_bijective adj ε
  intro K
  have he : (fun φ : K ⟶ P ↦ E'.map (L.map φ ≫ ε)) =
      (fun ψ ↦ c.hom.app K ≫ ψ) ∘ (fun φ ↦ L'.map φ ≫ δ) ∘ E.map := by
    funext φ
    simp only [Function.comp_apply, Functor.map_comp, hε, ← Category.assoc]
    simpa only [Functor.comp_map] using
      congrArg (fun ψ ↦ ψ ≫ δ) (c.hom.naturality φ)
  have hp : Function.Bijective fun ψ : L'.obj (E.obj K) ⟶ E'.obj T ↦ c.hom.app K ≫ ψ := by
    refine ⟨fun ψ ψ' hψ ↦ (cancel_epi _).1 hψ, fun ψ ↦ ⟨c.inv.app K ≫ ψ, ?_⟩⟩
    simp
  have hm : Function.Bijective (fun φ : K ⟶ P ↦ E.map φ) :=
    ⟨E.map_injective, E.map_surjective⟩
  have hb : Function.Bijective (fun φ : K ⟶ P ↦ E'.map (L.map φ ≫ ε)) := by
    rw [he]
    exact hp.comp ((h K).comp hm)
  refine ⟨fun φ ψ hφ ↦ hb.1 (congrArg E'.map hφ), fun ψ ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := hb.2 (E'.map ψ)
  exact ⟨φ, E'.map_injective hφ⟩

end CategoryTheory.Adjunction

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v

variable {C D : Type*} [Category.{v} C] [Category.{v} D]
  [Abelian C] [IsGrothendieckAbelian.{v} C]
  [Abelian D] [IsGrothendieckAbelian.{v} D]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v} (IsoAlgebra G)]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]

/-- A trace for a right derived Weil functor is universal if its carrier is universal
on the shifts of the source and the source is bounded. -/
theorem bijective_map_comp_rightDerived_of_bounded
    (hcoprod : ∀ (X : ℤ → DerivedCategory C) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L.rightDerivedFunctor)
    {P : DerivedCategory (IsoAlgebra F)} {T : DerivedCategory (IsoAlgebra G)}
    (ε : (mapOfNatIso e).rightDerivedFunctor.obj P ⟶ T)
    (K : DerivedCategory (IsoAlgebra F))
    (hK : DerivedCategory.TStructure.t.bounded ((forget F).mapDerivedCategory.obj K))
    (h : ∀ n : ℤ, Function.Bijective fun φ : (shiftFunctor _ n).obj
        ((forget F).mapDerivedCategory.obj K) ⟶ (forget F).mapDerivedCategory.obj P ↦
      L.rightDerivedFunctor.map φ ≫ (derivedForgetCommIso e).inv.app P ≫
        (forget G).mapDerivedCategory.map ε) :
    Function.Bijective fun φ : K ⟶ P ↦ (mapOfNatIso e).rightDerivedFunctor.map φ ≫ ε := by
  refine bijective_map_comp_of_bijective_forget F G _ _ (derivedForgetCommIso e) ε K ?_ h
  intro n
  obtain ⟨a, ha⟩ := (ObjectProperty.le_shift
    (P := DerivedCategory.TStructure.t.bounded) n _ hK).1
  have := ha
  exact isIso_derivedFreeComparison e hcoprod _ a

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The bounded-below coproduct theorem with the small index used by free Weil objects. -/
theorem condensed_trace_preservesCoproduct
    (K : ℤ → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (a : ℤ) (hK : ∀ n, (K n).IsGE a) :
    PreservesColimit (Discrete.functor K) (lowerStar Λ f).rightDerivedFunctor := by
  let e := Discrete.equivalence (Equiv.ulift.{u + 1} : ULift ℤ ≃ ℤ)
  have : PreservesColimit (Discrete.functor fun n : ULift.{u + 1} ℤ ↦ K n.down)
      (lowerStar Λ f).rightDerivedFunctor :=
    condensed_boundedBelow_preservesCoproduct Λ f _ a _ (fun n ↦ hK n.down)
  have : PreservesColimit (e.functor ⋙ Discrete.functor K)
      (lowerStar Λ f).rightDerivedFunctor :=
    preservesColimit_of_iso_diagram
      (K₁ := Discrete.functor fun n : ULift.{u + 1} ℤ ↦ K n.down)
      _ (Discrete.natIso fun _ ↦ Iso.refl _)
  exact Functor.Final.preservesColimit_of_comp e.functor

end AlgebraicGeometry.ProEtale.CondensedRing
