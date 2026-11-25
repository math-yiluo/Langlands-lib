/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.StrictlyHenselianBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ProperBaseChange

/-!
# Base change between strictly henselian local rings, module objects with finite coefficients

Let `T` be a finite discrete commutative ring and `T̲ = C(-, T)` its condensed ring. For a local
homomorphism `ι : R₁ ⟶ R₂` of strictly henselian local rings, morphisms `tᵢ : Spec Ωᵢ ⟶ Spec Rᵢ`
from spectra of separably closed fields, `c : Spec Ω₂ ⟶ Spec Ω₁` with `c ≫ t₁ = t₂ ≫ Spec ι`, and
`b : R₂ ⟶ κ` a map to a field with kernel the maximal ideal, the pullback along `Spec b` of the
base change morphism `L(Spec ι)^* Rt₁_* ⟶ Rt₂_* Lc^*` of module objects over `T̲` is invertible at
every complex bounded below of étale origin
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_of_isStrictlyHenselianLocalRing`). This is
`ProEtale.isIso_leftDerivedUpperStar_map_derivedBaseChangeMap_app_of_isStrictlyHenselianLocalRing`
read through the comparison `Φ` of module objects over `T̲` with pro-étale sheaves of
`T`-modules (`ProEtale.nonempty_arrowIso_map_baseChangeMap_finiteCoefficient`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Base change between strictly henselian local rings at the closed point**, for module
objects over `T̲ = C(-, T)`, `T` a finite discrete ring: in the situation of
`ProEtale.isIso_leftDerivedUpperStar_map_derivedBaseChangeMap_app_of_isStrictlyHenselianLocalRing`,
the pullback along `s = Spec b` of the base change morphism `Lι'^* Rt₁_* L ⟶ Rt₂_* Lc^* L`,
`ι' = Spec ι`, is an isomorphism for every `L` bounded below of étale origin. The schemes and the
morphisms `ι'`, `s` are given together with equations identifying them with spectra, so that the
statement applies verbatim to other presentations of them, for instance as the projections of the
models `NearbyCyclesModel.ofTrait`. -/
theorem isIso_map_baseChangeMap_app_of_isStrictlyHenselianLocalRing
    {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
    [IsStrictlyHenselianLocalRing R₂] (ι : R₁ →+* R₂) [IsLocalHom ι]
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂] [IsSepClosed Ω₂]
    {κ : Type u} [Field κ] (b : R₂ →+* κ) (hb : RingHom.ker b = IsLocalRing.maximalIdeal R₂)
    {S₁ S₂ G₁ G₂ P : Scheme.{u}} (eS₁ : S₁ = Spec (.of R₁)) (eS₂ : S₂ = Spec (.of R₂))
    (eG₁ : G₁ = Spec (.of Ω₁)) (eG₂ : G₂ = Spec (.of Ω₂)) (eP : P = Spec (.of κ))
    {t₁ : G₁ ⟶ S₁} {t₂ : G₂ ⟶ S₂} {c : G₂ ⟶ G₁} {ι' : S₂ ⟶ S₁}
    (hι : ι' = eqToHom eS₂ ≫ Spec.map (CommRingCat.ofHom ι) ≫ eqToHom eS₁.symm)
    (sq : CommSq c t₂ t₁ ι') {s : P ⟶ S₂}
    (hs : s = eqToHom eP ≫ Spec.map (CommRingCat.ofHom b) ≫ eqToHom eS₂.symm)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology G₁) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) G₁)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) _
      ((finiteCoefficientDerivedEquivalence _ T).functor.obj L)) :
    IsIso (L((s)^*⟦Profinite.continuousMapRingObj T⟧).map
      ((baseChangeMap (Profinite.continuousMapRingObj T) sq).app L)) := by
  subst eS₁ eS₂ eG₁ eG₂ eP
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hι hs
  subst hι hs
  have h := isIso_leftDerivedUpperStar_map_derivedBaseChangeMap_app_of_isStrictlyHenselianLocalRing
    (ULift.{u + 1} T) ι sq b hb _ hL
  obtain ⟨e⟩ := nonempty_arrowIso_map_baseChangeMap_finiteCoefficient (T := T) sq L
  have h₁ := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    ((L((Spec.map (CommRingCat.ofHom b))^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])).mapArrow.mapIso
      e)).2 h
  have h₂ := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (finiteCoefficientDerivedUpperStarIso T (Spec.map (CommRingCat.ofHom b)))
      (Arrow.mk ((baseChangeMap (Profinite.continuousMapRingObj T) sq).app L)))).2 h₁
  have : IsIso ((finiteCoefficientModEquivalence (Spec (.of κ)) T).functor.mapDerivedCategory.map
      (L((Spec.map (CommRingCat.ofHom b))^*⟦Profinite.continuousMapRingObj T⟧).map
        ((baseChangeMap (Profinite.continuousMapRingObj T) sq).app L))) := h₂
  exact isIso_of_reflects_iso _
    (finiteCoefficientModEquivalence (Spec (.of κ)) T).functor.mapDerivedCategory

end AlgebraicGeometry.ProEtale.CondensedRing
