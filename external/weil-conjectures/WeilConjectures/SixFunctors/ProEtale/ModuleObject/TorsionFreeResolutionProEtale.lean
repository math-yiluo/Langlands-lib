/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.TorsionFreeResolutionMod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueIsoCriterion

/-!
# Torsion-free `f_*`-acyclic resolutions on the pro-étale site

Let `Λ` be a commutative condensed ring, `X` a scheme, `r` an endomorphism of the regular
`Λ_X`-module and `ι_X : Λ_X ⟶ F_X` a monomorphism of `Λ_X`-modules such that `F_X ⊗ -` preserves
monomorphisms and `r` acts on `F_X` by an epimorphism (in the application: `ι : 𝒪_{E,X} ⟶ E_X`
and `r = ϖ`). Then every bounded below `K ∈ D(Λ_X)` is represented by a bounded below complex
`J` on whose terms `r` acts injectively and whose terms are `f_*`-acyclic for every `f : X ⟶ Y`
along which `ι_X` is the pullback of a monomorphism `ι_Y : Λ_Y ⟶ F_Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Every `Λ_Y`-module is a quotient of a module `M` such that `ι_X ▷ f^* M` is a monomorphism,
if `ι_X` is the pullback of a monomorphism `ι_Y`. -/
lemma exists_epi_mono_whiskerRight_upperStar_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    {FY : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (ιY : 𝟙_ _ ⟶ FY) [Mono ιY]
    {FX : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)} (ιX : 𝟙_ _ ⟶ FX)
    (e : (f)^*⟦Λ⟧.obj FY ≅ FX)
    (he : Functor.LaxMonoidal.ε (f)^*⟦Λ⟧ ≫ (f)^*⟦Λ⟧.map ιY ≫ e.hom = ιX)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ∃ (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (π : N ⟶ M),
      Epi π ∧ Mono (ιX ▷ (f)^*⟦Λ⟧.obj N) :=
  exists_epi_mono_whiskerRight_obj _ ιY ιX e he M

/-- **Torsion-free `f_*`-acyclic resolutions**: if `ι_X : Λ_X ⟶ F_X` is a monomorphism such that
`F_X ⊗ -` preserves monomorphisms and `r` acts on `F_X` by an epimorphism, every bounded below
`K ≥ n` in `D(Λ_X)` is represented by a complex `J ≥ n - 1` on whose terms `r` acts injectively
and whose terms are `f_*`-acyclic for every `f : X ⟶ Y` along which `ι_X` is the pullback of a
monomorphism `ι_Y : Λ_Y ⟶ F_Y`. -/
theorem exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic {X : Scheme.{u}}
    {FX : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)} (ιX : 𝟙_ _ ⟶ FX)
    [Mono ιX] [(tensorLeft FX).PreservesMonomorphisms]
    (r : 𝟙_ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⟶ 𝟙_ _)
    [Epi (Mod.regularEndSMul r FX)]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (n : ℤ) [K.IsGE n] :
    ∃ (J : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ),
      Nonempty (K ≅ DerivedCategory.Q.obj J) ∧ J.IsStrictlyGE (n - 1) ∧
      (∀ k, Mono (Mod.regularEndSMul r (J.X k))) ∧
      ∀ {Y : Scheme.{u}} (f : X ⟶ Y)
        {FY : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
        (ιY : 𝟙_ _ ⟶ FY) [Mono ιY] (e : (f)^*⟦Λ⟧.obj FY ≅ FX)
        (_ : Functor.LaxMonoidal.ε (f)^*⟦Λ⟧ ≫ (f)^*⟦Λ⟧.map ιY ≫ e.hom = ιX) (k : ℤ),
        ((f)_*⟦Λ⟧).rightAcyclic (J.X k) := by
  obtain ⟨J, e, hJ, hr, hG⟩ := Mod.exists_iso_Q_obj_mono_regularEndSMul ιX r K n
  exact ⟨J, e, hJ, hr, fun f _ ιY _ e he k ↦ hG (upperStarLowerStarAdjunction Λ f)
    (exists_epi_mono_whiskerRight_upperStar_obj Λ f ιY ιX e he) k⟩

end AlgebraicGeometry.ProEtale.CondensedRing
