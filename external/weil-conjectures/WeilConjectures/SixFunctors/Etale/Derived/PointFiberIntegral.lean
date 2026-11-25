/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegralMilnor
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegralUnit
public import WeilConjectures.SixFunctors.Etale.Derived.RationalStage

/-!
# Integral constructible complexes over a geometric point

Let `k` be a separably closed field and `Λ` a complete discrete valuation ring with finite
residue field, for instance the ring of integers `𝒪_E` of a finite extension `E` of `ℚ_ℓ`, with
maximal ideal `I = (ϖ)`. The integral stage `Dᵇc(Spec k, Λ)` of the `ℓ`-adic formalism
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`) consists of the objects
of `D((Spec k)_ét, Λ)` which are derived complete and whose reductions `K ⊗ᴸ Λ/Iⁿ⁺¹` are
bounded constructible of Tor amplitude in one common interval. This file shows that these are
exactly the bounded constructible objects, so that the global sections induce an equivalence

`Fib_s : Dᵇc(Spec k, Λ) ≌ Dᵇ_fg(Λ)`

with the bounded complexes of `Λ`-modules with finitely generated cohomology modules, all of which
are derived complete.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_iff_boundedConstructible`: on `Spec k`,
  the integral stage consists of the bounded constructible complexes.
- `AlgebraicGeometry.Etale.pointFiberIntegralEquivalence` and, for `Λ = 𝒪_E`,
  `AlgebraicGeometry.Etale.pointFiberIntegerRingEquivalence`
  (`lemma-perfect-complexes-geometric-point`, integral stage): `Fib_s : Dᵇc(Spec k, Λ) ≌ Dᵇ_fg(Λ)`.
- `DerivedCategory.boundedFiniteCohomology_rightOrthogonal`: the objects of `Dᵇ_fg(Λ)` are
  derived complete, i.e. receive no nonzero map from an object on which `ϖ` acts invertibly.

## Proof

If `K` is bounded constructible, the dévissage of bounded complexes reduces the claim to a
constructible sheaf, the constant sheaf on a finitely generated `Λ`-module, which is a cokernel of
a map of finite free modules; so it reduces to `Λ` placed in degree `0`. Its reductions are the
constant sheaves `Λ/Iⁿ⁺¹`, of Tor amplitude in `[-1, 0]` by the triangles `Λ ⟶ Λ ⟶ Λ/Iⁿ⁺¹`; and
`Λ` is derived complete, being the homotopy limit of the tower `Λ/Iⁿ`, as it is for modules
(`DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi`).

Conversely, let `K` be derived complete with reductions `Kₙ` of Tor amplitude in `[a, b]` with
constructible cohomology. Morphisms out of `Λ` placed in degree `j` compute the global sections of
the cohomology sheaves (`AlgebraicGeometry.Etale.homSingleLinearEquiv`), which for the `Kₙ` are
finite and vanish outside `[a, b]`. The Milnor sequence of the homotopy limit `K = R lim Kₙ`
then shows that `M = Hom(Λ[-j], K)` is the inverse limit of the finite groups
`Hom(Λ[-j], Kₙ)`: it vanishes outside `[a, b]`, it is `ϖ`-adically separated, and `M/ϖM`
embeds into `Hom(Λ[-j], K₁)`, so `M` is finitely generated
(`Module.finite_of_isHausdorff_of_ker_le`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] essentiallySmall_etale_pointFiberIntegral

section IntegralPoint

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsSepClosed k]

variable [IsNoetherianRing Λ] [Finite (Λ ⧸ I)]

variable [IsAdicComplete I Λ]

variable (k) in
/-- The constant sheaf on a `Λ`-module `M` on `Spec k`, placed in degree `0`. -/
noncomputable abbrev constSingle (M : ModuleCat.{u + 1} Λ) :
    DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)

omit [IsSepClosed k] [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] [IsAdicComplete I Λ] in
include hϖ hI in
lemma boundedConstructibleIntegral_constSingle_of_iso {M N : ModuleCat.{u + 1} Λ} (e : M ≅ N)
    (h : DerivedCategory.boundedConstructibleIntegral I (Spec (.of k)) (constSingle k M)) :
    DerivedCategory.boundedConstructibleIntegral I (Spec (.of k)) (constSingle k N) :=
  have := DerivedCategory.isClosedUnderIsomorphisms_boundedConstructibleIntegral
    (X := Spec (.of k)) hϖ hI
  (DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).prop_of_iso
    ((DerivedCategory.singleFunctor _ 0).mapIso ((constantSheaf _ _).mapIso e)) h

include hϖ hI in
/-- The constant sheaf `Λⁿ` on `Spec k`, placed in degree `0`, lies in the integral stage. -/
lemma boundedConstructibleIntegral_constSingle_free (n : ℕ) :
    DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))
      (constSingle k (ModuleCat.of Λ (Fin n → Λ))) := by
  induction n with
  | zero =>
    have := DerivedCategory.containsZero_boundedConstructibleIntegral (X := Spec (.of k)) hϖ hI
    have := DerivedCategory.isClosedUnderIsomorphisms_boundedConstructibleIntegral
      (X := Spec (.of k)) hϖ hI
    have := additive_constantSheaf Λ (Spec (.of k))
    exact ObjectProperty.prop_of_isZero _ (Functor.map_isZero _
      (Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _)))
  | succ n ih =>
    let e : ModuleCat.of Λ (Fin (n + 1) → Λ) ≅ ModuleCat.of Λ Λ ⊞ ModuleCat.of Λ (Fin n → Λ) :=
      (Fin.consLinearEquiv Λ (fun _ : Fin (n + 1) ↦ Λ)).symm.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd (ModuleCat.of Λ Λ) (ModuleCat.of Λ (Fin n → Λ))).symm
    refine boundedConstructibleIntegral_constSingle_of_iso hϖ hI e.symm ?_
    exact (boundedConstructibleIntegral_single_of_shortExact hϖ hI
      (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact).2
      (boundedConstructibleIntegral_unitSingle hϖ hI) ih

variable [IsDomain Λ] [IsPrincipalIdealRing Λ]

include hϖ hI in
/-- The constant sheaf on a finitely generated `Λ`-module `M`, placed in degree `0`, lies in the
integral stage: `M` is the cokernel of an injective map of finite free modules. -/
lemma boundedConstructibleIntegral_constSingle (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    DerivedCategory.boundedConstructibleIntegral I (Spec (.of k)) (constSingle k M) := by
  obtain ⟨s, π, hπ⟩ := Module.Finite.exists_fin' Λ M
  have : Module.Free Λ (LinearMap.ker π) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis Λ (LinearMap.ker π)
  let S := ModuleCat.shortComplexOfCompEqZero (LinearMap.ker π).subtype π (by ext; simp)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_ker_map π) Subtype.val_injective hπ
  exact (boundedConstructibleIntegral_single_of_shortExact hϖ hI hS).1
    (boundedConstructibleIntegral_constSingle_of_iso hϖ hI b.equivFun.toModuleIso.symm
      (boundedConstructibleIntegral_constSingle_free hϖ hI _))
    (boundedConstructibleIntegral_constSingle_free hϖ hI s)

include hϖ hI in
/-- Over a separably closed field `k`, a bounded constructible object of `D((Spec k)_ét, Λ)` lies
in the integral stage `Dᵇc(Spec k, Λ)`, by dévissage to constant sheaves on finitely generated
modules. -/
theorem boundedConstructibleIntegral_of_boundedConstructible
    {K : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) K) :
    DerivedCategory.boundedConstructibleIntegral I (Spec (.of k)) K := by
  have : Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ}) := ⟨⟨ϖ, hϖ, hI⟩⟩
  have := DerivedCategory.isClosedUnderIsomorphisms_boundedConstructibleIntegral
    (X := Spec (.of k)) hϖ hI
  refine _root_.DerivedCategory.prop_of_bounded _
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) (Spec (.of k))) (fun F hF ↦ ?_) K hK.1 hK.2
  have := (isConstructibleSheaf_iff_moduleFinite_pointSections F).1 hF
  exact (DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).prop_of_iso
    ((DerivedCategory.singleFunctor _ 0).mapIso
      ((constantSheafEquivalenceOfIsSepClosed Λ (k := k)).counitIso.app F))
    (boundedConstructibleIntegral_constSingle hϖ hI ((pointSections Λ k).obj F))

include hϖ hI in
/-- Over a separably closed field `k`, the integral stage `Dᵇc(Spec k, Λ)` consists exactly of the
bounded constructible objects of `D((Spec k)_ét, Λ)`. -/
theorem boundedConstructibleIntegral_iff_boundedConstructible
    (K : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.boundedConstructibleIntegral I (Spec (.of k)) K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) K :=
  ⟨boundedConstructible_of_boundedConstructibleIntegral hϖ hI,
    boundedConstructibleIntegral_of_boundedConstructible hϖ hI⟩

variable (I k) [Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})]

/-- The evaluation at the geometric point of `s = Spec k`, `Fib_s : Dᵇc(s, Λ) ⥤ Dᵇ_fg(Λ)` at the
integral stage: the restriction of `D(Γ)` to the integral stage, with values in the bounded
complexes of `Λ`-modules with finitely generated cohomology. -/
noncomputable def pointFiberIntegral :
    (DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).FullSubcategory ⥤
      _root_.DerivedCategory.BoundedFiniteCohomology Λ :=
  (_root_.DerivedCategory.boundedFiniteCohomology Λ).lift
    ((DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).ι ⋙
      (pointSections Λ k).mapDerivedCategory)
    (fun K ↦ (boundedConstructible_iff_boundedFiniteCohomology K.obj).1
      (boundedConstructible_of_boundedConstructibleIntegral
        (Fact.out : ∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ}).choose_spec.1
        (Fact.out : ∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ}).choose_spec.2 K.property))

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finite coefficient categories over a point
(integral stage `𝒪_E`).

Let `Λ` be a complete discrete valuation ring with finite residue field and maximal ideal
`I = (ϖ)` (in the blueprint `Λ = 𝒪_E`, see
`AlgebraicGeometry.Etale.pointFiberIntegerRingEquivalence`) and `k` a separably closed field. The
evaluation at the geometric point of `s = Spec k`,
`Fib_s : Dᵇc(s, Λ) ⥤ Dᵇ_fg(Λ)` (`AlgebraicGeometry.Etale.pointFiberIntegral`), is an equivalence
from the integral stage `Dᵇc(s, Λ)` (derived complete objects of `D(s_ét, Λ)` whose reductions
modulo `Iⁿ⁺¹` are bounded constructible of uniformly bounded Tor amplitude,
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`) onto the bounded
complexes of `Λ`-modules with finitely generated cohomology modules. These complexes are derived
complete (`DerivedCategory.boundedFiniteCohomology_rightOrthogonal`), so that the target is the
category `Dᵇ_fg(𝒪_E)` of bounded derived-complete complexes with finitely generated cohomology of
the blueprint. It is the restriction of the equivalence `D(Γ) : D(s_ét, Λ) ≌ D(Λ)`, the integral
stage over `s` being the bounded constructible objects
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_iff_boundedConstructible`). -/
noncomputable def pointFiberIntegralEquivalence :
    (DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).FullSubcategory ≌
      _root_.DerivedCategory.BoundedFiniteCohomology Λ :=
  letI : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.functor.Additive :=
    additive_sheafSections_obj Λ _
  letI : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.inverse.Additive :=
    additive_constantSheaf Λ _
  (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.mapDerivedCategory.congrFullSubcategory
    (by
      ext K
      obtain ⟨ϖ, hϖ, hI⟩ := (Fact.out : ∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})
      exact ((boundedConstructibleIntegral_iff_boundedConstructible hϖ hI K).trans
        (boundedConstructible_iff_boundedFiniteCohomology K)).symm)

lemma pointFiberIntegralEquivalence_functor :
    (pointFiberIntegralEquivalence I k).functor = pointFiberIntegral I k :=
  rfl

instance : (pointFiberIntegral I k).IsEquivalence :=
  inferInstanceAs (pointFiberIntegralEquivalence I k).functor.IsEquivalence

end IntegralPoint

/-! ### The objects of `Dᵇ_fg(Λ)` are derived complete -/

section DerivedComplete

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] [IsAdicComplete I Λ]
  [IsDomain Λ] [IsPrincipalIdealRing Λ]

include hϖ hI in
/-- The bounded complexes of modules with finitely generated cohomology over a complete discrete
valuation ring `Λ` with finite residue field and maximal ideal `I = (ϖ)` are derived complete:
they receive no nonzero morphism from an object on which `ϖ` acts invertibly. They are the
images under `D(Γ)` of integral objects over a separably closed point, which are derived
complete. -/
theorem _root_.DerivedCategory.boundedFiniteCohomology_rightOrthogonal
    {L : _root_.DerivedCategory (ModuleCat.{u + 1} Λ)}
    (hL : _root_.DerivedCategory.boundedFiniteCohomology Λ L)
    {Y : _root_.DerivedCategory (ModuleCat.{u + 1} Λ)} (hY : IsIso (ϖ • 𝟙 Y)) (f : Y ⟶ L) :
    f = 0 := by
  -- any separably closed field will do
  let k : Type u := AlgebraicClosure (ULift.{u} (ZMod 2))
  have hϖI : ϖ ∈ I := hI ▸ Ideal.mem_span_singleton_self ϖ
  have : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.functor.Additive :=
    additive_sheafSections_obj Λ _
  have : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.inverse.Additive :=
    additive_constantSheaf Λ _
  let E := (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.mapDerivedCategory
  have : E.functor.Linear Λ := inferInstanceAs ((pointSections Λ k).mapDerivedCategory.Linear Λ)
  let eL : E.functor.obj (E.inverse.obj L) ≅ L := E.counitIso.app L
  let eY : E.functor.obj (E.inverse.obj Y) ≅ Y := E.counitIso.app Y
  have hL' : DerivedCategory.boundedConstructibleIntegral I (Spec (.of k)) (E.inverse.obj L) :=
    (boundedConstructibleIntegral_iff_boundedConstructible hϖ hI _).2
      ((boundedConstructible_iff_boundedFiniteCohomology _).2
        ((_root_.DerivedCategory.boundedFiniteCohomology Λ).prop_of_iso eL.symm hL))
  have hY' : IsIso (ϖ • 𝟙 (E.inverse.obj Y)) := by
    have : IsIso (E.functor.map (ϖ • 𝟙 (E.inverse.obj Y))) := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
      have : ϖ • 𝟙 (E.functor.obj (E.inverse.obj Y)) = eY.hom ≫ (ϖ • 𝟙 Y) ≫ eY.inv := by
        rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.hom_inv_id]
      rw [this]
      infer_instance
    exact isIso_of_fully_faithful E.functor _
  have h0 := _root_.DerivedCategory.rightOrthogonal_of_derivedComplete hϖI hL'.1
    (E.functor.preimage (eY.hom ≫ f ≫ eL.inv)) hY'
  have : eY.hom ≫ f ≫ eL.inv = 0 := by
    rw [← E.functor.map_preimage (eY.hom ≫ f ≫ eL.inv), h0, Functor.map_zero]
  rwa [← cancel_epi eY.hom, ← cancel_mono eL.inv, Limits.comp_zero, Limits.zero_comp,
    Category.assoc]

end DerivedComplete

/-! ### The ring of integers of a finite extension of `ℚ_ℓ` -/

section IntegerRing

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k] [IsSepClosed k]

/-- The residue field `𝒪_E/𝔪_E` of the universe `u + 1` copy of the ring of integers of a finite
extension `E` of `ℚ_ℓ` is finite. -/
instance _root_.PadicAlgCl.finite_quotient_maximalIdealShrink :
    Finite (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸ PadicAlgCl.maximalIdealShrink l E) :=
  have : Finite (PadicAlgCl.integers l E ⧸ IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (PadicAlgCl.integers l E)))
  Finite.of_equiv _ (Ideal.quotientEquiv _ _ (PadicAlgCl.shrinkRingEquiv l E) rfl).toEquiv

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finite coefficient categories over a point
(integral stage `𝒪_E`).

For a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and a separably closed field `k`, evaluation at
the geometric point of `s = Spec k` is an equivalence
`Fib_s : Dᵇc(s, 𝒪_E) ≌ Dᵇ_fg(𝒪_E)` between the integral stage
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral 𝔪_E s` and the bounded
complexes of `𝒪_E`-modules with finitely generated cohomology modules (which are derived
complete, `DerivedCategory.boundedFiniteCohomology_rightOrthogonal`). This is
`AlgebraicGeometry.Etale.pointFiberIntegralEquivalence` for `Λ = 𝒪_E`, whose maximal ideal is
generated by a nonzerodivisor (`PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span`).
The finite stage is `AlgebraicGeometry.Etale.pointFiberEquivalence`. -/
noncomputable def pointFiberIntegerRingEquivalence :
    (DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E)
      (Spec (.of k))).FullSubcategory ≌
      _root_.DerivedCategory.BoundedFiniteCohomology (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  haveI : Fact (∃ ϖ ∈ nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)),
      PadicAlgCl.maximalIdealShrink l E = Ideal.span {ϖ}) :=
    ⟨PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E⟩
  pointFiberIntegralEquivalence _ k

end IntegerRing

end Etale

end AlgebraicGeometry
