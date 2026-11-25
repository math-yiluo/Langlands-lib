/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModelOfClass
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfectAdic
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary

/-!
# Point perfectness of global sections, with amplitudes

Blueprint `lemma-perfect-complexes-geometric-point`. Let `k` be a separably closed field, `X` a
separated scheme of finite type over `k` with structure morphism `a_X`, and `d` a bound for the
dimension of `X` (and of all its base changes to fields). For `K ∈ Dctf(X, Λ)` of Tor amplitude in
`[a, b]`, the complexes `RΓ(X, K)`, `RΓ_c(X, K)` and their duals `RHom_Λ(-, Λ)` are perfect point
complexes (`DerivedCategory.IsPerfect`); this file adds the amplitude bounds of the blueprint.

## Main statements

- `DerivedCategory.exists_iso_Q_obj_of_torAmplitudeIn`
(`lemma-perfect-complexes-geometric-point--1`):
  over a Noetherian ring, a complex of Tor amplitude in `[a, b]` with finitely generated
  cohomology is represented by a complex of finite projective modules in degrees `[a, b]`.
- `DerivedCategory.torAmplitudeIn_ihom_unit`: its dual then has Tor amplitude in `[-b, -a]`.
- `AlgebraicGeometry.Etale.torAmplitudeIn_globalSections`: the amplitudes `[a, b + 2d]` and
  `[-b - 2d, -a]` of the finite stage of `lemma-perfect-complexes-geometric-point`.
- `AlgebraicGeometry.Etale.nonempty_iso_tensor_compactlySupportedGlobalSections` and
  `AlgebraicGeometry.Etale.nonempty_iso_tensor_rightDerivedGlobalSections`: over a domain, the
  reductions modulo a principal ideal of the global sections are the global sections of the
  reductions.

Perfectness at all stages (`AlgebraicGeometry.Etale.isPerfect_globalSections`,
`AlgebraicGeometry.Etale.isPerfect_globalSections_integral`,
`AlgebraicGeometry.ProEtale.isPerfect_globalSections_adic`) is in
`WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [HasDerivedCategory.{u} (ModuleCat.{u} R)]

omit [IsNoetherianRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)] in
/-- Finite projective modules lift along epimorphisms onto finite modules: a finite module is a
quotient of a finite free module, which lifts along any surjection. -/
private lemma liftsAlongEpi_projective_finite :
    ChainComplex.LiftsAlongEpi (C := ModuleCat.{u} R)
      (fun M ↦ Module.Projective R M ∧ Module.Finite R M) (fun M ↦ Module.Finite R M) := by
  intro A B G p _ g hG
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R G
  obtain ⟨h, hh⟩ := Module.projective_lifting_property p.hom (g.hom ∘ₗ π)
    ((ModuleCat.epi_iff_surjective p).1 inferInstance)
  refine ⟨ModuleCat.of R (Fin n → R), ModuleCat.ofHom π, ModuleCat.ofHom h,
    ⟨inferInstance, inferInstance⟩, (ModuleCat.epi_iff_surjective _).2 hπ, ?_⟩
  ext1
  exact hh

/-- Blueprint `lemma-perfect-complexes-geometric-point--1`: over a Noetherian ring `R`, a complex
`C` with finitely generated cohomology modules and Tor amplitude in `[a, b]` is quasi-isomorphic to
a complex of finite projective `R`-modules concentrated in degrees `[a, b]`.

It is the bounded flat model of `C` in degrees `[a, b]` built from a resolution by finite
projective modules (`DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi`
for the classes of finite projective and of finite modules); its terms are finite and flat,
hence projective. -/
theorem exists_iso_Q_obj_of_torAmplitudeIn {a b : ℤ} {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : torAmplitudeIn (ModuleCat.{u} R) a b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) ∧ Nonempty (C ≅ Q.obj P) := by
  let T : ObjectProperty (ModuleCat.{u} R) := fun M ↦ Module.Finite R M
  let S : ObjectProperty (ModuleCat.{u} R) := fun M ↦ Module.Projective R M ∧ Module.Finite R M
  have : T.IsClosedUnderIsomorphisms := ⟨fun e (h : Module.Finite R _) ↦
    Module.Finite.equiv e.toLinearEquiv⟩
  have : S.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    have := h.1; have := h.2
    ⟨Module.Projective.of_equiv e.toLinearEquiv, Module.Finite.equiv e.toLinearEquiv⟩⟩
  have : T.ContainsZero := ⟨ModuleCat.of R PUnit.{u + 1}, ModuleCat.isZero_of_subsingleton _,
    (inferInstance : Module.Finite R PUnit.{u + 1})⟩
  have : S.ContainsZero := ⟨ModuleCat.of R PUnit.{u + 1}, ModuleCat.isZero_of_subsingleton _,
    (inferInstance : Module.Projective R PUnit.{u + 1}),
    (inferInstance : Module.Finite R PUnit.{u + 1})⟩
  have : T.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, hX, hY⟩
    have : Module.Finite R _ := hX
    refine T.prop_of_iso (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk) ?_
    exact Module.Finite.equiv (ModuleCat.kernelIsoKer f).symm.toLinearEquiv⟩
  have : T.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hX, hY⟩
    have : Module.Finite R _ := hY
    refine T.prop_of_iso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hk) ?_
    exact Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient f).symm.toLinearEquiv⟩
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ :=
    exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi (S := S) (T := T)
      (fun _ h ↦ h.2)
      (fun M h ↦ by
        have := h.1
        exact (ModuleCat.flat_iff_flat M).2 inferInstance)
      (fun X Y hX hY ↦ by
        have := hX.1; have := hX.2; have := hY.1; have := hY.2
        exact ⟨Module.Projective.of_equiv (ModuleCat.biprodIsoProd X Y).symm.toLinearEquiv,
          Module.Finite.equiv (ModuleCat.biprodIsoProd X Y).symm.toLinearEquiv⟩)
      liftsAlongEpi_projective_finite hC hfin
  refine ⟨P, inferInstance, inferInstance, fun i ↦ ?_, ⟨e.symm⟩⟩
  have : Module.Flat R (P.X i) := (ModuleCat.flat_iff_flat _).1 (hP i).1
  have : Module.Finite R (P.X i) := (hP i).2
  have := Module.finitePresentation_of_finite R (P.X i)
  exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

omit [IsNoetherianRing R] in
/-- The dual `RHom_R(P, R)` of a complex `P` of finite projective modules concentrated in
degrees `[a, b]` has Tor amplitude in `[-b, -a]`: it is represented by the termwise dual
complex `Hom_R(P^{-i}, R)`, a complex of finite projective (hence flat) modules in degrees
`[-b, -a]`. The computation of the dual is that of `DerivedCategory.IsPerfect.ihom_unit`. -/
theorem torAmplitudeIn_ihom_unit_Q_obj (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) :
    torAmplitudeIn (ModuleCat.{u} R) (-b) (-a) ((ihom (Q.obj P)).obj (𝟙_ _)) := by
  have hd (n : ℤ) : IsDualizable (P.X n) := by
    have := (hP n).1
    have := (hP n).2
    exact ModuleCat.isDualizable_of_projective (P.X n)
  let _ : ∀ n, HasRightDual (P.X n) := fun n ↦ (hd n).some
  let _ := CochainComplex.exactPairingRightDual P a b
  let H := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  have hd' (n : ℤ) : IsDualizable (P.rightDual.X n) :=
    ⟨{ rightDual := P.X (-n)
       exact := (BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ :) }⟩
  let X : (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P a b (fun n ↦ (hd n).flat))⟩
  let Y : (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P.rightDual, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P.rightDual (-b) (-a)
        (fun n ↦ (hd' n).flat))⟩
  let _ : ExactPairing ((ObjectProperty.ι _).obj X) ((ObjectProperty.ι _).obj Y) :=
    ExactPairing.map H P P.rightDual
  let _ : ExactPairing X Y := ExactPairing.ofFullyFaithful (ObjectProperty.ι _) X Y
  let _ := Functor.Monoidal.ofLaxMonoidal (kFlatQh (ModuleCat.{u} R))
  let _ : ExactPairing ((kFlatQh (ModuleCat.{u} R)).obj X)
      ((kFlatQh (ModuleCat.{u} R)).obj Y) :=
    ExactPairing.map (kFlatQh (ModuleCat.{u} R)) X Y
  let _ : HasRightDual ((kFlatQh (ModuleCat.{u} R)).obj X) :=
    ⟨(kFlatQh (ModuleCat.{u} R)).obj Y⟩
  obtain ⟨_⟩ := nonempty_braidedCategory (ModuleCat.{u} R)
  let f : (ihom (Q.obj P)).obj (𝟙_ _) ≅ Q.obj P.rightDual :=
    (MonoidalClosed.internalHom.mapIso ((quotientCompQhIso _).app P).op).app _ ≪≫
      ihomUnitIsoRightDual ((kFlatQh (ModuleCat.{u} R)).obj X) ≪≫
      (quotientCompQhIso _).app P.rightDual
  exact (torAmplitudeIn _ (-b) (-a)).prop_of_iso f.symm
    (torAmplitudeIn_Q_obj_of_flat P.rightDual (-b) (-a) fun n ↦ (hd' n).flat)

/-- The dual of a perfect point complex, with amplitude (Step 1 of blueprint
`lemma-perfect-complexes-geometric-point`): over a Noetherian ring, if `C` has finitely generated
cohomology and Tor amplitude in `[a, b]`, then `C^∨ = RHom_R(C, R)` has Tor amplitude in
`[-b, -a]`. -/
theorem torAmplitudeIn_ihom_unit {a b : ℤ} {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : torAmplitudeIn (ModuleCat.{u} R) a b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    torAmplitudeIn (ModuleCat.{u} R) (-b) (-a) ((ihom C).obj (𝟙_ _)) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_of_torAmplitudeIn hC hfin
  exact (torAmplitudeIn _ (-b) (-a)).prop_of_iso
    ((MonoidalClosed.internalHom.mapIso e.op).app _) (torAmplitudeIn_ihom_unit_Q_obj P a b hP)

end DerivedCategory

namespace AlgebraicGeometry

open Scheme Opposite

namespace Etale

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [HasCompactification aX] (d : ℕ)
  (hd : ∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of k)) {P : Scheme.{u}}
    (p₁ : P ⟶ X) (p₂ : P ⟶ Spec (.of L)), IsPullback p₁ p₂ aX s →
      topologicalKrullDim P ≤ (d : WithBot ℕ∞))

include hd in
/-- Blueprint `lemma-perfect-complexes-geometric-point` (Step 1, compact support): **Tor amplitude
of `RΓ_c(X, K)`.** Let `Λ` be finite with exponent invertible in the separably closed field `k`,
and let `d` bound the dimension of every base change of `X` to a field (for `X` of finite type
over `k` this is a bound for `dim X`). If `K` has Tor amplitude in `[a, b]`, then `RΓ_c(X, K)`
has Tor amplitude in `[a, b + 2d]`: by the projection formula
`Ra_{X!} K ⊗ᴸ F ≅ Ra_{X!}(K ⊗ᴸ a_X^* F)`, and `Ra_{X!}` is left t-exact of cohomological
amplitude `2d`. This is the argument of
`AlgebraicGeometry.Etale.finiteTorAmplitude_compactlySupportedGlobalSections`, keeping track
of the bound. -/
theorem torAmplitudeIn_compactlySupportedGlobalSections (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hta : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) a (b + 2 * (d : ℤ))
      ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K) := by
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom aX
  refine torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed
    ((DerivedCategory.torAmplitudeIn_iff_derivedTensor _ _ a (b + 2 * d) _).2 fun F ↦ ?_)
  replace hta := (DerivedCategory.torAmplitudeIn_iff_derivedTensor _ _ a b K).1 hta
  obtain ⟨e⟩ := nonempty_iso_tensor_singleFunctor_obj_rightDerivedLowerShriek Λ aX K F
  let M := ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj ((aX)^*[ModuleCat.{u + 1} Λ].obj F))
  obtain ⟨hMa, hMb⟩ := hta ((aX)^*[ModuleCat.{u + 1} Λ].obj F)
  have : M.IsGE a := hMa
  have : M.IsLE b := hMb
  have hM : _root_.DerivedCategory.TStructure.t.bounded M := ⟨⟨a, hMa⟩, ⟨b, hMb⟩⟩
  have := isGE_rightDerivedLowerShriek_obj Λ aX M hM a
  have : ((R(aX)_![ModuleCat.{u + 1} Λ]).obj M).IsLE (b + 2 * d) := by
    refine _root_.DerivedCategory.isLE_obj_of_isLE (R(aX)_![ModuleCat.{u + 1} Λ]) (2 * d)
      (fun F ↦ ?_) M hM b
    rw [_root_.DerivedCategory.isLE_iff]
    exact fun i hi ↦ isZero_homology_rightDerivedLowerShriek_singleFunctor Λ aX aX (𝟙 _)
      (Category.comp_id _) d (fun Ω _ _ s ↦ hd Ω s _ _ (IsPullback.of_hasPullback aX s)) F i
      (by lia)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm (b + 2 * d)⟩

omit [HasCompactification aX] in
include hd in
/-- Blueprint `lemma-perfect-complexes-geometric-point` (Step 1, ordinary cohomology): **Tor
amplitude of `RΓ(X, K)`.** In the situation of
`AlgebraicGeometry.Etale.torAmplitudeIn_compactlySupportedGlobalSections`, for `X` separated
and `K ∈ Dctf(X, Λ)` of Tor amplitude in `[a, b]`, the complex `RΓ(X, K) = RΓ(k, Ra_{X*} K)`
has Tor amplitude in `[a, b + 2d]`: `Ra_{X*} K` has Tor amplitude in `[a, b + 2d]`
(`cor-sf-direct-image-ctf`, `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`),
and over the separably closed `k` the global sections are a stalk. No properness is used. -/
theorem torAmplitudeIn_rightDerivedGlobalSections_of_le [IsSeparated aX] (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) a (b + 2 * (d : ℤ))
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K) := by
  have hdX : topologicalKrullDim X ≤ (d : WithBot ℕ∞) :=
    hd k (𝟙 _) (𝟙 X) aX IsPullback.of_id_fst
  obtain ⟨N, hN0, hNΛ, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of k))
  have : NeZero N := ⟨hN0.ne'⟩
  have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ K
  exact (_root_.DerivedCategory.torAmplitudeIn _ _ _).prop_of_iso
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aX).app K)
    (torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed
      (torAmplitudeIn_rightDerivedLowerStar _ aX (𝟙 _) aX (Category.comp_id _) d hdX a b N hN
        hNY hbc hta))

include hd in
/-- Blueprint `lemma-perfect-complexes-geometric-point`, finite level (Step 1), the amplitudes.

Let `Λ = A_{E,n}` be a finite ring whose exponent is invertible in the separably closed field
`k`, `X` a separated scheme of finite type over `k` with structure morphism `a_X`, and `d` a
bound for the dimension of every base change of `X` to a field (in particular `dim X ≤ d`). Let
`K ∈ Dctf(X, Λ)` have Tor amplitude in `[a, b]`. Then `RΓ_c(X, K)` and `RΓ(X, K)` have Tor
amplitude in `[a, b + 2d]`, and their duals `RHom_Λ(-, Λ)` have Tor amplitude in
`[-b - 2d, -a]`. Neither properness nor smoothness of `X` is assumed.

Perfectness of the four complexes is `AlgebraicGeometry.Etale.isPerfect_globalSections`; the
amplitudes are `AlgebraicGeometry.Etale.torAmplitudeIn_compactlySupportedGlobalSections`,
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedGlobalSections_of_le`, and for the duals
the termwise dual of a finite projective model in degrees `[a, b + 2d]`
(`DerivedCategory.torAmplitudeIn_ihom_unit`, `lemma-perfect-complexes-geometric-point--1`). -/
theorem torAmplitudeIn_globalSections [IsSeparated aX] (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) a (b + 2 * (d : ℤ))
        ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K) ∧
      _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) a (b + 2 * (d : ℤ))
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K) ∧
      _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) (-(b + 2 * (d : ℤ))) (-a)
        ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K)).obj
          (𝟙_ _)) ∧
      _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) (-(b + 2 * (d : ℤ))) (-a)
        ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj (𝟙_ _)) := by
  have hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K := ⟨hbc, a, b, hta⟩
  have hc := isPerfect_compactlySupportedGlobalSections Λ aX K hK
  have hr := isPerfect_rightDerivedGlobalSections Λ aX K hK
  have htc := torAmplitudeIn_compactlySupportedGlobalSections Λ aX d hd a b K hta
  have htr := torAmplitudeIn_rightDerivedGlobalSections_of_le Λ aX d hd a b K hbc hta
  exact ⟨htc, htr, _root_.DerivedCategory.torAmplitudeIn_ihom_unit htc hc.finite_homology,
    _root_.DerivedCategory.torAmplitudeIn_ihom_unit htr hr.finite_homology⟩

end Finite

section Reduction

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] {k : Type u} [Field k] [IsSepClosed k]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))

variable (Λ) in
/-- Over a separably closed field `k`, the derived global sections of the constant sheaf `M`
placed in degree `0` are `M` placed in degree `0`. -/
noncomputable def rightDerivedGlobalSectionsSingleConstantSheafIso (M : ModuleCat.{u + 1} Λ) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj M :=
  (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app _ ≪≫
    (((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (op (etalePoint k))).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (asIso ((constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
        isTerminalEtalePoint).unit.app M)).symm

/-- Blueprint `lemma-perfect-complexes-geometric-point` (Step 2, compact support): **reduction of
`RΓ_c(X, K)`.** Over a separably closed field `k`, for a principal ideal `J` of the domain `Λ`,
the reduction of the compactly supported cohomology is the compactly supported cohomology of
the reduction: `RΓ_c(X, K) ⊗ᴸ_Λ Λ/J ≅ RΓ_c(X, K ⊗ᴸ (Λ/J)_X)`. It combines the compatibility of
`RΓ(k, -)` with derived tensor products and the commutation of `Ra_{X!}` with reduction
(`lemma-change-coefficients-compact-support`,
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isPrincipal`). -/
theorem nonempty_iso_tensor_compactlySupportedGlobalSections [HasCompactification aX]
    (J : Ideal Λ) (hJ : J.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K ⊗
        (_root_.DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of Λ (Λ ⧸ J)) ≅
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj
        ((reductionModIdeal Λ X J).obj K)) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedGlobalSections_derivedTensor_of_isSepClosed Λ
    ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K) ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))))
  obtain ⟨e₂⟩ := nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isPrincipal Λ aX J hJ
  exact ⟨(MonoidalCategory.whiskerLeftIso _
      (rightDerivedGlobalSectionsSingleConstantSheafIso Λ _)).symm ≪≫ e₁.symm ≪≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso (e₂.app K)⟩

include aX in
/-- Blueprint `lemma-perfect-complexes-geometric-point` (Step 2, ordinary cohomology): **reduction
of `RΓ(X, K)`.** Over a separably closed field `k`, for a principal ideal `J` of the domain `Λ`,
`RΓ(X, K) ⊗ᴸ_Λ Λ/J ≅ RΓ(X, K ⊗ᴸ (Λ/J)_X)`: write `RΓ(X, -) = RΓ(k, Ra_{X*} -)`, use that
`Ra_{X*}` commutes with reduction (`lemma-change-coefficients-direct-image--1`,
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`) and that
`RΓ(k, -)` is compatible with derived tensor products. -/
theorem nonempty_iso_tensor_rightDerivedGlobalSections (J : Ideal Λ) (hJ : J.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K ⊗
        (_root_.DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of Λ (Λ ⧸ J)) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        ((reductionModIdeal Λ X J).obj K)) := by
  let eΓ := rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) aX
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedGlobalSections_derivedTensor_of_isSepClosed Λ
    (((aX)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.obj K)
    ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))))
  obtain ⟨e₂⟩ := nonempty_iso_reductionModIdeal_rightDerivedLowerStar Λ aX J hJ
  exact ⟨MonoidalCategory.whiskerRightIso (eΓ.app K).symm _ ≪≫
    (MonoidalCategory.whiskerLeftIso _
      (rightDerivedGlobalSectionsSingleConstantSheafIso Λ _)).symm ≪≫ e₁.symm ≪≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso (e₂.app K) ≪≫
    eΓ.app _⟩

end Reduction

end Etale

end AlgebraicGeometry
