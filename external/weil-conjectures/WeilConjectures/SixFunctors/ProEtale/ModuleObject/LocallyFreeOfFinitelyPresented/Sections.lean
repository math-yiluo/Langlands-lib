/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.Mathlib.CategoryTheory.Conj
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections

/-!
# Sections of `ℚ̲̄_ℓ,W` over a quasi-compact quasi-separated scheme

Let `Λ` be a commutative condensed ring and `Λ_W` its pullback to the pro-étale site of a scheme
`W`. The endomorphisms of the regular module `Λ_W` are the global sections `Γ(W, Λ_W)`
(`CategoryTheory.Mod.regularEndRingHom_bijective`). Along a morphism `g : W' ⟶ W` they restrict
by the ring homomorphism `ProEtale.CondensedRing.restrictEnd`: apply the pullback `g^*` and
conjugate by `g^* Λ_W ≅ Λ_{W'}`.

For `Λ = ℚ̲̄_ℓ` and `W` quasi-compact and quasi-separated, `Γ(W, ℚ̲̄_ℓ,W)` is the ring of continuous
functions `W → ℚ̄_ℓ` with values in a finite subextension of `ℚ̄_ℓ / ℚ_ℓ`
(`PadicAlgCl.finiteIntermediateFieldValued`), restriction being precomposition
(`ProEtale.CondensedRing.exists_endRegularRingEquiv`). This is Bhatt–Scholze, *The pro-étale
topology for schemes*, Lemma 4.2.12 and §6.8: the pullback of the condensed ring `C(-, E)` to the
pro-étale site is `U ↦ C(U, E)` for a finite subextension `E`
(`ProEtale.isIso_continuousMapComparison`), and for `W` quasi-compact and
quasi-separated taking sections commutes with the filtered colimit `ℚ̲̄_ℓ = colim_E E̲`
(`ProEtale.padicAlgClSectionRingEquiv`). On global sections, the restriction of endomorphisms is
the pullback followed by `α_g` (`ProEtale.CondensedRing.restrictEnd_regularEndRingHom`).

## Main definitions

- `ProEtale.CondensedRing.restrictEnd`: restriction of endomorphisms of the regular module.
- `ProEtale.CondensedRing.endRegularRingEquiv`: `End (Λ_W) ≃+* {continuous finite-valued
  functions W → ℚ̄_ℓ}` for `W` quasi-compact and quasi-separated.

## Main results

- `ProEtale.CondensedRing.endRegularRingEquiv_restrictEnd`: compatibility with restriction.
- `ProEtale.CondensedRing.isIso_of_forall_ne_zero`: an endomorphism of `ℚ̲̄_ℓ,W` whose function
  vanishes nowhere is invertible.
- `ProEtale.CondensedRing.exists_endRegularRingEquiv_eq_const`: constant functions are sections.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Restrict

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The restriction `Γ(W, Λ_W) → Γ(W', Λ_{W'})` along `g : W' ⟶ W`, on the endomorphisms of the
regular modules: the pullback `g^*` followed by conjugation with `g^* Λ_W ≅ Λ_{W'}`. -/
noncomputable def restrictEnd {W' W : Scheme.{u}} (g : W' ⟶ W) :
    End (Mod.regular (condensedRingObj Λ W)) →+* End (Mod.regular (condensedRingObj Λ W')) :=
  (upperStarObjRegularIso Λ g).conjRingEquiv.toRingHom.comp
    (((g)^*⟦Λ⟧).mapEndRingHom (Mod.regular (condensedRingObj Λ W)))

lemma restrictEnd_apply {W' W : Scheme.{u}} (g : W' ⟶ W)
    (t : End (Mod.regular (condensedRingObj Λ W))) :
    restrictEnd Λ g t =
      .of ((upperStarObjRegularIso Λ g).inv ≫ (g)^*⟦Λ⟧.map t.asHom ≫
        (upperStarObjRegularIso Λ g).hom) :=
  rfl

/-- On global sections, the restriction of endomorphisms of the regular module is the pullback
`Γ(W, Λ_W) → Γ(W', g^* Λ_W)` followed by `α_g : g^* Λ_W ≅ Λ_{W'}`. -/
lemma restrictEnd_regularEndRingHom {W' W : Scheme.{u}} (g : W' ⟶ W)
    (s : Γ (condensedRingObj Λ W)) :
    restrictEnd Λ g (Mod.regularEndRingHom s) =
      Mod.regularEndRingHom
        (Γ.map (condensedPullbackHom Λ g) (Γ.mapFunctor (g)^*[Ab.{u + 1}] s)) := by
  rw [restrictEnd_apply]
  apply End.ext
  have h₁ : (g)^*⟦Λ⟧.map (Mod.regularEndRingHom s).asHom =
      (Mod.extendScalars (condensedPullbackHom Λ g)).map
        (Mod.regularEndRingHom (Γ.mapFunctor (g)^*[Ab.{u + 1}] s)).asHom := by
    rw [← Functor.mapMod_map_regularEndRingHom]
    rfl
  have nat : (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)).inv.app
        (((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ W)).obj
          (Mod.regular (condensedRingObj Λ W))) ≫
      (Mod.extendScalars (condensedPullbackHom Λ g)).map
        (Mod.regularEndRingHom (Γ.mapFunctor (g)^*[Ab.{u + 1}] s)).asHom ≫
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)).hom.app
        (((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ W)).obj
          (Mod.regular (condensedRingObj Λ W))) =
      (Mod.comap (asIso (condensedPullbackHom Λ g)).inv).map
        (Mod.regularEndRingHom (Γ.mapFunctor (g)^*[Ab.{u + 1}] s)).asHom :=
    NatIso.naturality_1 _ _
  rw [h₁, upperStarObjRegularIso, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [reassoc_of% nat]
  refine Mod.regular_hom_ext ?_
  rw [Mod.comp_hom', Mod.comp_hom', Mod.regularEndRingHom_apply, Mod.regularEndRingHom_apply]
  have hR₁ : (Mod.regularIsoOfIsIso (condensedPullbackHom Λ g)).inv.hom =
      inv (condensedPullbackHom Λ g) := rfl
  have hR₂ : (Mod.regularIsoOfIsIso (condensedPullbackHom Λ g)).hom.hom =
      condensedPullbackHom Λ g := rfl
  rw [hR₁, hR₂, Mod.comap_map_hom, ← Category.assoc]
  erw [IsMonHom.one_hom (inv (condensedPullbackHom Λ g))]
  rw [← Category.assoc, Mod.one_comp_regularLift_regular, Γ.map_hom]
  exact congrArg (· ≫ condensedPullbackHom Λ g)
    (Mod.one_comp_regularLift_regular (Γ.mapFunctor (g)^*[Ab.{u + 1}] s).hom)

end Restrict

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Sections of `ℚ̲̄_ℓ` over a quasi-compact quasi-separated scheme.**

For every quasi-compact quasi-separated scheme `W` there is a ring isomorphism from the
endomorphisms of the regular module `ℚ̲̄_ℓ,W` (that is, from `Γ(W, ℚ̲̄_ℓ,W)`) onto the continuous
functions `W → ℚ̄_ℓ` with values in a finite subextension, compatible with restriction along every
morphism `g : W' ⟶ W`, which on functions is precomposition with `g`.

This is Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 4.2.12 together with the
description of `ℚ̄_ℓ,W = colim_E E_W` of §6.8. The endomorphisms of the regular module are the
global sections (`CategoryTheory.Mod.regularEndRingHom_bijective`), whose restriction is computed
by `ProEtale.CondensedRing.restrictEnd_regularEndRingHom`; the global sections of `ℚ̲̄_ℓ,W` are
computed by `ProEtale.padicAlgClSectionRingEquiv`, compatibly with pullback
(`ProEtale.Γ_map_condensedPullbackHom_padicAlgClSectionRingHom`). The proof uses
`ProEtale.isIso_continuousMapComparison`: the pullback of `C(-, E)` from the point
is the sheaf `U ↦ C(U, E)`. -/
theorem exists_endRegularRingEquiv :
    ∃ e : ∀ (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W],
        End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)) ≃+*
          PadicAlgCl.finiteIntermediateFieldValued ℓ W,
      ∀ (W' W : Scheme.{u}) [CompactSpace W'] [QuasiSeparatedSpace W'] [CompactSpace W]
        [QuasiSeparatedSpace W] (g : W' ⟶ W)
        (t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)))
        (x : W'),
        (e W' (restrictEnd _ g t) : C(W', PadicAlgCl ℓ)) x = (e W t : C(W, PadicAlgCl ℓ)) (g x) :=
  by
  have key (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W]
      (f : PadicAlgCl.finiteIntermediateFieldValued ℓ W) :
      ((RingEquiv.ofBijective _ Mod.regularEndRingHom_bijective).symm.trans
        (padicAlgClSectionRingEquiv ℓ W).symm)
        (Mod.regularEndRingHom (padicAlgClSectionRingHom ℓ W f)) = f := by
    rw [RingEquiv.trans_apply, ← RingEquiv.ofBijective_apply _ Mod.regularEndRingHom_bijective,
      RingEquiv.symm_apply_apply]
    exact (padicAlgClSectionRingEquiv ℓ W).symm_apply_apply f
  refine ⟨fun W _ _ ↦ (RingEquiv.ofBijective _ Mod.regularEndRingHom_bijective).symm.trans
    (padicAlgClSectionRingEquiv ℓ W).symm, fun W' W _ _ _ _ g t x ↦ ?_⟩
  obtain ⟨s, rfl⟩ := Mod.regularEndRingHom_bijective.2 t
  obtain ⟨f, rfl⟩ := (padicAlgClSectionRingHom_bijective ℓ W).2 s
  rw [restrictEnd_regularEndRingHom, Γ_map_condensedPullbackHom_padicAlgClSectionRingHom, key,
    key]
  rfl

/-- The ring isomorphism `Γ(W, ℚ̲̄_ℓ,W) ≃+* {continuous finite-valued functions W → ℚ̄_ℓ}` for a
quasi-compact quasi-separated scheme `W`. -/
noncomputable def endRegularRingEquiv (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W] :
    End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)) ≃+*
      PadicAlgCl.finiteIntermediateFieldValued ℓ W :=
  (exists_endRegularRingEquiv ℓ).choose W

/-- The value at a point `x` of the function of an endomorphism of `ℚ̲̄_ℓ,W`. -/
noncomputable def endValue {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    (t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W))) (x : W) :
    PadicAlgCl ℓ :=
  (endRegularRingEquiv ℓ W t : C(W, PadicAlgCl ℓ)) x

/-- Restriction is precomposition on values. -/
lemma endValue_restrictEnd {W' W : Scheme.{u}} [CompactSpace W'] [QuasiSeparatedSpace W']
    [CompactSpace W] [QuasiSeparatedSpace W] (g : W' ⟶ W)
    (t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W))) (x : W') :
    endValue ℓ (restrictEnd _ g t) x = endValue ℓ t (g x) :=
  (exists_endRegularRingEquiv ℓ).choose_spec W' W g t x

section Values

variable {ℓ} {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]

/-- Evaluation at a point, as a ring homomorphism `Γ(W, ℚ̲̄_ℓ,W) →+* ℚ̄_ℓ`. -/
noncomputable def endValueRingHom (x : W) :
    End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)) →+*
      PadicAlgCl ℓ :=
  (((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom).comp
    (PadicAlgCl.finiteIntermediateFieldValued ℓ W).subtype).comp
    (endRegularRingEquiv ℓ W).toRingHom

@[simp]
lemma endValueRingHom_apply (x : W)
    (t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W))) :
    endValueRingHom x t = endValue ℓ t x :=
  rfl

lemma continuous_endValue
    (t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W))) :
    Continuous (endValue ℓ t) :=
  (endRegularRingEquiv ℓ W t : C(W, PadicAlgCl ℓ)).continuous

/-- An endomorphism of `ℚ̲̄_ℓ,W` is determined by its values. -/
lemma endValue_injective
    {t t' : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W))}
    (h : ∀ x, endValue ℓ t x = endValue ℓ t' x) : t = t' :=
  (endRegularRingEquiv ℓ W).injective (Subtype.ext (ContinuousMap.ext h))

lemma eq_zero_of_forall_endValue_eq_zero
    {t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W))}
    (h : ∀ x, endValue ℓ t x = 0) : t = 0 :=
  endValue_injective fun x ↦ by rw [h x, ← endValueRingHom_apply, map_zero]

/-- A continuous finite-valued function vanishing nowhere is a unit of the ring of such
functions: its pointwise inverse is continuous, with values in the same finite subextension. -/
lemma isUnit_of_forall_ne_zero {X : Type*} [TopologicalSpace X]
    (f : PadicAlgCl.finiteIntermediateFieldValued ℓ X) (hf : ∀ x, (f : C(X, PadicAlgCl ℓ)) x ≠ 0) :
    IsUnit f := by
  obtain ⟨E, hE, hfE⟩ := f.2
  let g : C(X, PadicAlgCl ℓ) := ⟨fun x ↦ ((f : C(X, PadicAlgCl ℓ)) x)⁻¹,
    (f : C(X, PadicAlgCl ℓ)).continuous.inv₀ hf⟩
  have hg : g ∈ PadicAlgCl.finiteIntermediateFieldValued ℓ X :=
    ⟨E, hE, fun x ↦ inv_mem (hfE x)⟩
  refine IsUnit.of_mul_eq_one ⟨g, hg⟩ (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
  exact mul_inv_cancel₀ (hf x)

/-- An endomorphism of `ℚ̲̄_ℓ,W` whose function vanishes nowhere is invertible. -/
lemma isIso_of_forall_ne_zero
    (t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)))
    (ht : ∀ x, endValue ℓ t x ≠ 0) : IsIso t.asHom := by
  rw [← isUnit_iff_isIso]
  exact (isUnit_map_iff (endRegularRingEquiv ℓ W) t).1 (isUnit_of_forall_ne_zero _ ht)

/-- Over a scheme with at most one point, every nonzero endomorphism of `ℚ̲̄_ℓ,W` is
invertible. -/
lemma isIso_of_ne_zero_of_subsingleton [Subsingleton W]
    (t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)))
    (ht : t ≠ 0) : IsIso t.asHom := by
  refine isIso_of_forall_ne_zero t fun x hx ↦ ht (eq_zero_of_forall_endValue_eq_zero fun y ↦ ?_)
  rwa [Subsingleton.elim y x]

/-- Every element `c` of `ℚ̄_ℓ` is the constant value of a section of `ℚ̲̄_ℓ,W`: `c` lies in the
finite subextension `ℚ_ℓ(c)`. -/
lemma exists_endValue_eq_const (c : PadicAlgCl ℓ) :
    ∃ t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)),
      ∀ x, endValue ℓ t x = c := by
  have hc : _root_.IsIntegral ℚ_[ℓ] c := Algebra.IsIntegral.isIntegral c
  have hmem : ContinuousMap.const W c ∈ PadicAlgCl.finiteIntermediateFieldValued ℓ W :=
    ⟨IntermediateField.adjoin ℚ_[ℓ] {c}, IntermediateField.adjoin.finiteDimensional hc,
      fun _ ↦ IntermediateField.mem_adjoin_simple_self ℚ_[ℓ] c⟩
  refine ⟨(endRegularRingEquiv ℓ W).symm ⟨_, hmem⟩, fun x ↦ ?_⟩
  simp [endValue]

end Values

end AlgebraicGeometry.ProEtale.CondensedRing
