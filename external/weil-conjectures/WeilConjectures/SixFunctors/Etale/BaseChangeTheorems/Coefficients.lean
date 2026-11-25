/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedRestrictScalars.IsIso

/-!
# Change of coefficients for the base change property

Let `Λ` be a commutative ring and `N` a positive integer, and put `Λ_N = Λ ⧸ NΛ`. Restriction of
scalars along `Λ ⟶ Λ_N` is exact and conservative, commutes with `g^*` and `f_*`, and commutes
with `Rf_*`: an injective sheaf of `Λ_N`-modules has no higher cohomology as a sheaf of
`Λ`-modules. It therefore carries the derived base change map over `Λ_N` to the one over `Λ`.

Consequently:

- the base change property with `Λ`-coefficients implies the one with `Λ_N`-coefficients
  (`AlgebraicGeometry.Etale.HasTorsionBaseChange.quotient`), since a complex of sheaves of
  `Λ_N`-modules has torsion cohomology as a complex of sheaves of `Λ`-modules;
- for a quasi-compact quasi-separated `f`, the base change property with `Λ_p`-coefficients for
  every prime `p` implies the one with `Λ`-coefficients
  (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_forall_prime`): by truncation an object of
  `D⁺` with torsion cohomology is reduced to a torsion sheaf in one degree, a torsion sheaf is a
  filtered colimit of sheaves killed by integers, which are successive extensions of sheaves
  killed by primes (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf`),
  and a sheaf of `Λ`-modules killed by `p` is a sheaf of `Λ_p`-modules.

This is the change of coefficients in the proof of the reduction of proper base change to the
projective line (blueprint `proposition-proper-base-change-etale-site--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The quotient `Λ ⧸ NΛ` of a ring by a positive integer is torsion as an additive group: it is
killed by `N`. -/
lemma isAddTorsion_quotient_span_natCast {N : ℕ} (hN : 0 < N) :
    IsAddTorsion (Λ ⧸ Ideal.span {(N : Λ)}) := fun x ↦
  (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨N, hN, by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk _), ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)⟩

section RestrictScalars

variable {Λ} {Λ' : Type (u + 1)} [CommRing Λ'] (φ : Λ →+* Λ')

/-- A sheaf of `Λ'`-modules is torsion if and only if its restriction of scalars along
`φ : Λ →+* Λ'` is: both have the same underlying sheaf of abelian groups. -/
lemma Scheme.isTorsionModuleSheaf_restrictScalars_obj_iff {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    IsTorsionModuleSheaf ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F) ↔
      IsTorsionModuleSheaf F := by
  rw [isTorsionModuleSheaf_iff_isTorsion, isTorsionModuleSheaf_iff_isTorsion]
  rfl

/-- The restriction of scalars of a complex with torsion cohomology has torsion cohomology: its
cohomology sheaves are the restrictions of scalars of those of the complex. -/
lemma Etale.DerivedCategory.Plus.moduleTorsionHomology_restrictScalars {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')))
    (hK : Etale.DerivedCategory.Plus.moduleTorsionHomology Λ' X K) :
    Etale.DerivedCategory.Plus.moduleTorsionHomology Λ X
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K) := fun n ↦
  have := hK n
  have : IsTorsionModuleSheaf ((DerivedCategory.Plus.homologyFunctor _ n ⋙
      Sheaf.restrictScalars X.smallEtaleTopology φ).obj K) :=
    (Scheme.isTorsionModuleSheaf_restrictScalars_obj_iff φ _).2 this
  IsTorsionModuleSheaf.of_epi
    ((((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusHomologyFunctorIso
      n).app K).hom)

end RestrictScalars

/-- A sheaf of `Λ`-modules killed by an integer `r` is a sheaf of `Λ ⧸ rΛ`-modules: the counit
`res(Hom_Λ(Λ ⧸ rΛ, E)) ⟶ E` of restriction and coextension of scalars along `Λ ⟶ Λ ⧸ rΛ` is an
isomorphism. -/
lemma Etale.isIso_restrictCoextendScalarsAdj_counit_app_of_nsmul_eq_zero {X : Scheme.{u}}
    (r : ℕ) (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hE : r • 𝟙 E = 0) :
    IsIso ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology
      (Ideal.Quotient.mk (Ideal.span {(r : Λ)}))).counit.app E) := by
  have (U : X.Etaleᵒᵖ) : IsIso (((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology
      (Ideal.Quotient.mk (Ideal.span {(r : Λ)}))).counit.app E).hom.app U) := by
    rw [Etale.restrictCoextendScalarsAdj_counit_app_hom_app]
    let S := ModuleCat.coextendQuotientShortComplex (r : Λ) (E.obj.obj U)
    have hg : S.g = 0 := by
      have h := congrArg (fun a ↦ ((sheafToPresheaf _ _).map a).app U) hE
      simp only [Functor.map_nsmul, NatTrans.app_nsmul, CategoryTheory.Functor.map_id,
        NatTrans.id_app, Functor.map_zero, NatTrans.app_zero] at h
      change (r : Λ) • 𝟙 (E.obj.obj U) = 0
      rw [Nat.cast_smul_eq_nsmul]
      exact h
    have := (ModuleCat.exact_coextendQuotientShortComplex (r : Λ) (E.obj.obj U)).epi_f hg
    have := ModuleCat.mono_coextendQuotientShortComplex_f (r : Λ) (E.obj.obj U)
    exact isIso_of_mono_of_epi S.f
  have : ∀ U, IsIso (((sheafToPresheaf _ _).map ((Sheaf.restrictCoextendScalarsAdj
      X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {(r : Λ)}))).counit.app E)).app U) :=
    this
  have : IsIso ((sheafToPresheaf _ _).map ((Sheaf.restrictCoextendScalarsAdj
      X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {(r : Λ)}))).counit.app E)) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- **Base change property along a change of coefficient rings.** If `f` satisfies the base
change property with `Λ`-coefficients, then also with `Λ'`-coefficients for every ring
homomorphism `φ : Λ →+* Λ'`: restriction of scalars along `φ` reflects isomorphisms, preserves
torsion cohomology, and carries the derived base change map over `Λ'` to the one over `Λ`. -/
theorem Etale.HasTorsionBaseChange.of_ringHom {Λ' : Type (u + 1)} [CommRing Λ'] (φ : Λ →+* Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : Etale.HasTorsionBaseChange Λ f) :
    Etale.HasTorsionBaseChange Λ' f := by
  intro Y' X' g f' g' sq K hK
  rw [← Etale.isIso_derivedBaseChangeMapPlus_app_restrictScalars_iff φ sq.toCommSq K]
  exact hf sq _ (Etale.DerivedCategory.Plus.moduleTorsionHomology_restrictScalars φ K hK)

/-- **Base change property for a quotient coefficient ring.** If `f` satisfies the base change
property with `Λ`-coefficients, then also with `Λ ⧸ NΛ`-coefficients: restriction of scalars
along `Λ ⟶ Λ ⧸ NΛ` is conservative, sends complexes of `Λ ⧸ NΛ`-modules to complexes with
torsion cohomology, and carries the derived base change map over `Λ ⧸ NΛ` to the one over `Λ`.
(blueprint: `proposition-proper-base-change-etale-site--1`, change of coefficients) -/
theorem Etale.HasTorsionBaseChange.quotient {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : Etale.HasTorsionBaseChange Λ f) (N : ℕ) :
    Etale.HasTorsionBaseChange (Λ ⧸ Ideal.span {(N : Λ)}) f := by
  intro Y' X' g f' g' sq K hK
  rw [← Etale.isIso_derivedBaseChangeMapPlus_app_restrictScalars_iff
    (Ideal.Quotient.mk (Ideal.span {(N : Λ)})) sq.toCommSq K]
  exact hf sq _ (Etale.DerivedCategory.Plus.moduleTorsionHomology_restrictScalars _ K hK)

/-- **Base change property from prime coefficient rings.** Let `f` be quasi-compact and
quasi-separated. If `f` satisfies the base change property with `Λ ⧸ pΛ`-coefficients for every
prime `p`, then also with `Λ`-coefficients.
(blueprint: `proposition-proper-base-change-etale-site--1`, change of coefficients;
`theorem-pbc-injective-acyclicity--1`, from prime to arbitrary torsion) -/
theorem Etale.hasTorsionBaseChange_of_forall_prime {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (h : ∀ p : ℕ, p.Prime → Etale.HasTorsionBaseChange (Λ ⧸ Ideal.span {(p : Λ)}) f) :
    Etale.HasTorsionBaseChange Λ f := by
  intro Y' X' g f' g' sq K hK
  rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus]
  have hprime : ∀ r : ℕ, r.Prime → ∀ E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      r • 𝟙 E = 0 → ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E) := by
    intro r hr E hE
    rw [← Etale.isIso_baseChange_app_singleFunctor_obj_iff,
      Etale.baseChange_eq_derivedBaseChangeMapPlus]
    let φ := Ideal.Quotient.mk (Ideal.span {(r : Λ)})
    have := Etale.isIso_restrictCoextendScalarsAdj_counit_app_of_nsmul_eq_zero Λ r E hE
    let E' := (Etale.coextendScalars φ X).obj E
    let e : (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj E') ≅
        (DerivedCategory.Plus.singleFunctor _ 0).obj E :=
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusSingleFunctor 0).app
        E' ≪≫ (DerivedCategory.Plus.singleFunctor _ 0).mapIso
          (asIso ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).counit.app E))
    rw [← NatTrans.isIso_app_iff_of_iso _ e,
      Etale.isIso_derivedBaseChangeMapPlus_app_restrictScalars_iff]
    exact h r hr sq _ (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion _ _
      (isAddTorsion_quotient_span_natCast Λ hr.pos) _)
  let P : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun F ↦ IsTorsionModuleSheaf F
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    have : IsTorsionModuleSheaf _ := h
    IsTorsionModuleSheaf.of_epi e.hom⟩
  exact DerivedCategory.Plus.isIso_app_of_forall_homology _ P
    (fun F hF ↦ (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).2 fun q ↦
      have : IsTorsionModuleSheaf F := hF
      Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf Λ sq hprime F q)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeSource_obj Λ g f K n q hq)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ g' f' K n q hq) K hK

/-- **Injective acyclicity implies the base change property.** If a proper morphism
`f : X ⟶ Y` has injective acyclicity with `Λ ⧸ pΛ`-coefficients for every prime `p`, then it
satisfies the base change property with `Λ`-coefficients: for the torsion rings `Λ ⧸ pΛ` this is
`AlgebraicGeometry.Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity`, and the passage to `Λ`
is `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_forall_prime`.
(blueprint: `theorem-pbc-injective-acyclicity--1`, `IA_r(f)` for every prime `r` implies
`PBC(f)`) -/
@[stacks 0A4B]
theorem Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (hf : ∀ p : ℕ, p.Prime → Etale.HasInjectiveAcyclicity (Λ ⧸ Ideal.span {(p : Λ)}) f) :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_forall_prime Λ f fun p hp ↦
    (Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity _
      (isAddTorsion_quotient_span_natCast Λ hp.pos) f).2 (hf p hp)

end AlgebraicGeometry
