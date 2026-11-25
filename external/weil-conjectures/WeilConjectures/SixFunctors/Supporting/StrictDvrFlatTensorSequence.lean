/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.StrictDvrCoefficientSequence
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement

/-! # Flat tensor realization of the strict DVR coefficient sequence

Source: Stacks Project, Tag 0942, proof of lemma-bounded (1); Modules on Sites,
Tags 03EK and 03ER.
(blueprint: lem-sf-strict-dvr-flat-tensor-sequence)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u v r wR wS

open CategoryTheory CategoryTheory.Limits Opposite

open scoped ChangeOfRings

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

private instance (priority := 4000) strictDvrSiteSmall :
    EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf.{u} X.ProEt

private instance strictDvrRingSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      CommRingCat.{max u (t + 1)} := integralCoefficientRingSheafify.{t, u} X

private instance strictDvrAbSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X

private instance strictDvrAbLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X

open SheafOfModules

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralReductionExistence scalarReductionExistence
  unrestrictedIntegralTransition unrestrictedTowerTransition

private theorem reduction_obj_eq (n : ℕ) (M : scalarReductionSource l E X) :
    (scalarReductionExtension l E X n).obj M =
      (ordinaryExtension.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingProjectionUnrestricted l E X n)).obj M := by
  exact (scalarReductionExistence l E X n).choose_spec.choose M

private theorem reduction_map_eq (n : ℕ) {M N : scalarReductionSource l E X}
    (f : M ⟶ N) :
    (scalarReductionExtension l E X n).map f = eqToHom (reduction_obj_eq l E X n M) ≫
      (ordinaryExtension.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingProjectionUnrestricted l E X n)).map f ≫
          eqToHom (reduction_obj_eq l E X n N).symm := by
  exact (scalarReductionExistence l E X n).choose_spec.choose_spec.choose f

@[irreducible]
private def reductionOrdinaryIso (n : ℕ) :
    scalarReductionExtension l E X n ≅
      ordinaryExtension.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingProjectionUnrestricted l E X n) :=
  NatIso.ofComponents
    (fun M ↦ eqToIso (reduction_obj_eq l E X n M)) (by
      intro M N f
      simp only [eqToIso.hom,
        reduction_map_eq l E X n f,
        Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

@[irreducible]
private def reductionTensorIso (n : ℕ) :
    leftTensorSheaf (B := completedIntegralCommRingSheafUnrestricted l E X)
      (strictDvrFiniteCoefficient l E X n) ≅
      scalarReductionExtension l E X n ⋙ scalarReductionRestriction l E X n :=
  tensorExtensionIso.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingProjectionUnrestricted l E X n) ≪≫
    Functor.isoWhiskerRight (reductionOrdinaryIso l E X n).symm
      (scalarReductionRestriction l E X n)

private theorem reductionTensorIso_tmul (n : ℕ)
    (M : scalarReductionSource l E X) (U : X.ProEtᵒᵖ)
    (s : (strictDvrFiniteCoefficient l E X n).val.obj U) (x : M.val.obj U) :
    ((reductionTensorIso l E X n).hom.app M).val.app U
      (SheafOfModules.siteSheafTensorTmul.{t + 1, t, max u (t + 1), max u (t + 1)}
        (A := completedIntegralCommRingSheafUnrestricted l E X) (strictDvrFiniteCoefficient l E X
          n) M U s x) =
        unrestrictedTowerTensorSection l E X n M U s x := by
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      CommRingCat.{max u (t + 1)} := integralCoefficientRingSheafify.{t, u} X
  unfold reductionTensorIso reductionOrdinaryIso
  let g := (eqToHom (reduction_obj_eq l E X n M).symm).val.app U
  exact congrArg (fun y ↦ g y)
    (extensionTensorIso_tmul.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingProjectionUnrestricted l E X n) M U s x)

@[irreducible]
private def reductionTensorMap {n m : ℕ}
    (a : strictDvrFiniteCoefficient l E X n ⟶ strictDvrFiniteCoefficient l E X m) :
    scalarReductionExtension l E X n ⋙ scalarReductionRestriction l E X n ⟶
      scalarReductionExtension l E X m ⋙ scalarReductionRestriction l E X m :=
  (reductionTensorIso l E X n).inv ≫ leftTensorSheafMap.{t + 1, t, max u (t + 1)} a ≫
    (reductionTensorIso l E X m).hom

private theorem reductionTensorMap_tmul {n m : ℕ}
    (a : strictDvrFiniteCoefficient l E X n ⟶ strictDvrFiniteCoefficient l E X m)
    (M : scalarReductionSource l E X) (U : X.ProEtᵒᵖ)
    (s : (strictDvrFiniteCoefficient l E X n).val.obj U) (x : M.val.obj U) :
    ((reductionTensorMap l E X a).app M).val.app U
      (unrestrictedTowerTensorSection l E X n M U s x) =
        unrestrictedTowerTensorSection l E X m M U (a.val.app U s) x := by
  rw [← reductionTensorIso_tmul l E X n]
  unfold reductionTensorMap
  change ((reductionTensorIso l E X m).hom.app M).val.app U
    (((leftTensorSheafMap.{t + 1, t, max u (t + 1)} a).app M).val.app U
      (((reductionTensorIso l E X n).inv.app M).val.app U
        (((reductionTensorIso l E X n).hom.app M).val.app U _))) = _
  have h := congrArg (fun f ↦ f.val.app U
    (SheafOfModules.siteSheafTensorTmul.{t + 1, t, max u (t + 1), max u (t + 1)}
        (A := completedIntegralCommRingSheafUnrestricted l E X) (strictDvrFiniteCoefficient l E X
          n) M U s x))
    ((reductionTensorIso l E X n).app M).hom_inv_id
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at h
  exact (congrArg (fun y ↦ ((reductionTensorIso l E X m).hom.app M).val.app U
      (((leftTensorSheafMap.{t + 1, t, max u (t + 1)} a).app M).val.app U y)) h).trans
    ((congrArg (((reductionTensorIso l E X m).hom.app M).val.app U)
      (tensorMap_tmul.{t + 1, t, max u (t + 1)} a M U s x)).trans (reductionTensorIso_tmul l E X
        m M U _ x))

@[irreducible]
private def reductionChainMap {n m : ℕ}
    (a : strictDvrFiniteCoefficient l E X n ⟶ strictDvrFiniteCoefficient l E X m) :
    unrestrictedIntegralComplexFunctor l E X n ⟶ unrestrictedIntegralComplexFunctor l E X m := by
  change (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ) ⋙
      (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ) ⟶
    (scalarReductionExtension l E X m).mapHomologicalComplex (.up ℤ) ⋙
      (scalarReductionRestriction l E X m).mapHomologicalComplex (.up ℤ)
  exact
    { app := fun P ↦
        { f := fun j ↦ (reductionTensorMap l E X a).app (P.X j)
          comm' := fun j k _ ↦ ((reductionTensorMap l E X a).naturality (P.d j k)).symm }
      naturality := fun P Q f ↦ by
        ext j : 1
        exact (reductionTensorMap l E X a).naturality (f.f j) }

private theorem reductionChainMap_f {n m : ℕ}
    (a : strictDvrFiniteCoefficient l E X n ⟶ strictDvrFiniteCoefficient l E X m)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) (j : ℤ) :
    (((reductionChainMap l E X a).app P).f j) =
      (reductionTensorMap l E X a).app (P.X j) := by
  unfold reductionChainMap
  rfl

private theorem reductionChainMap_quotient (n : ℕ) :
    reductionChainMap l E X (strictDvrCoefficientQuotient l E X n) =
      unrestrictedIntegralTransition l E X n := by
  apply (unrestrictedIntegralTransition_existsUnique l E X n).unique
  · intro P j U s x
    rw [reductionChainMap_f]
    exact reductionTensorMap_tmul l E X (strictDvrCoefficientQuotient l E X n)
      (P.X j) U s x
  · intro P j U s x
    unfold unrestrictedIntegralTransition
    exact (unrestrictedIntegralTransition_existsUnique l E X n).exists.choose_spec P j U s x

private theorem reductionTensorMap_comp {n m k : ℕ}
    (a : strictDvrFiniteCoefficient l E X n ⟶ strictDvrFiniteCoefficient l E X m)
    (b : strictDvrFiniteCoefficient l E X m ⟶ strictDvrFiniteCoefficient l E X k)
    (M : scalarReductionSource l E X) :
    (reductionTensorMap l E X a).app M ≫ (reductionTensorMap l E X b).app M =
      (reductionTensorMap l E X (a ≫ b)).app M := by
  simp [reductionTensorMap, ← NatTrans.comp_app, leftTensorSheafMap_comp]

private theorem reductionTensorMap_zero (n m : ℕ) (M : scalarReductionSource l E X) :
    (reductionTensorMap l E X (0 : strictDvrFiniteCoefficient l E X n ⟶
      strictDvrFiniteCoefficient l E X m)).app M = 0 := by
  simp [reductionTensorMap, leftTensorSheafMap_zero]

@[irreducible]
private def reductionMap {n m : ℕ}
    (a : strictDvrFiniteCoefficient l E X n ⟶ strictDvrFiniteCoefficient l E X m)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    unrestrictedTowerComplex l E X n P ⟶ unrestrictedTowerComplex l E X m P :=
  (reductionChainMap l E X a).app P

private theorem reductionMap_f {n m : ℕ}
    (a : strictDvrFiniteCoefficient l E X n ⟶ strictDvrFiniteCoefficient l E X m)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) (j : ℤ) :
    (reductionMap l E X a P).f j = (reductionTensorMap l E X a).app (P.X j) := by
  unfold reductionMap
  exact reductionChainMap_f l E X a P j

private theorem reductionMap_quotient (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    reductionMap l E X (strictDvrCoefficientQuotient l E X n) P =
      unrestrictedTowerTransition l E X P n := by
  unfold reductionMap unrestrictedTowerTransition
  exact congrArg (fun τ ↦ τ.app P) (reductionChainMap_quotient l E X n)

private theorem reductionMap_comp {n m k : ℕ}
    (a : strictDvrFiniteCoefficient l E X n ⟶ strictDvrFiniteCoefficient l E X m)
    (b : strictDvrFiniteCoefficient l E X m ⟶ strictDvrFiniteCoefficient l E X k)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    reductionMap l E X a P ≫ reductionMap l E X b P =
      reductionMap l E X (a ≫ b) P := by
  apply HomologicalComplex.hom_ext
  intro j
  simp only [HomologicalComplex.comp_f, reductionMap_f]
  exact reductionTensorMap_comp l E X a b (P.X j)

private theorem reductionMap_zero (n m : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    reductionMap l E X (0 : strictDvrFiniteCoefficient l E X n ⟶
      strictDvrFiniteCoefficient l E X m) P = 0 := by
  apply HomologicalComplex.hom_ext
  intro j
  simp only [HomologicalComplex.zero_f, reductionMap_f]
  exact reductionTensorMap_zero l E X n m (P.X j)

private theorem reductionTensorMap_shortExact {n m k : ℕ}
    (a : strictDvrFiniteCoefficient l E X n ⟶ strictDvrFiniteCoefficient l E X m)
    (b : strictDvrFiniteCoefficient l E X m ⟶ strictDvrFiniteCoefficient l E X k)
    (hab : a ≫ b = 0) (hseq : (ShortComplex.mk a b hab).ShortExact)
    (M : scalarReductionSource l E X)
    (hflat : SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) M)
    (hz : (reductionTensorMap l E X a).app M ≫
      (reductionTensorMap l E X b).app M = 0) :
    (ShortComplex.mk ((reductionTensorMap l E X a).app M)
      ((reductionTensorMap l E X b).app M) hz).ShortExact := by
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      CommRingCat.{max u (t + 1)} := integralCoefficientRingSheafify.{t, u} X
  have : PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t + 1), max
    u (t + 1)}
      (A := completedIntegralCommRingSheafUnrestricted l E X) M) := hflat.1
  have : PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t + 1),
    max u (t + 1)}
      (A := completedIntegralCommRingSheafUnrestricted l E X) M) := hflat.2
  let S := (ShortComplex.mk a b hab).map (SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t
    + 1), max u (t + 1)}
      (A := completedIntegralCommRingSheafUnrestricted l E X) M)
  let T := ShortComplex.mk ((reductionTensorMap l E X a).app M)
    ((reductionTensorMap l E X b).app M) hz
  have e : S ≅ T := by
    refine ShortComplex.isoMk ((reductionTensorIso l E X n).app M)
      ((reductionTensorIso l E X m).app M) ((reductionTensorIso l E X k).app M) ?_ ?_
    · simp [S, T, reductionTensorMap, leftTensorSheafMap]
    · simp [S, T, reductionTensorMap, leftTensorSheafMap]
  exact ShortComplex.shortExact_of_iso e
    (hseq.map_of_exact (SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t + 1), max u (t + 1)}
      (A := completedIntegralCommRingSheafUnrestricted l E X) M))

/-- Tensor an exact coefficient sequence with a flat-term complex, using the actual
unrestricted reduction complexes and their prescribed quotient chain transitions.

Source: Stacks Project, Tag 0942, proof of lemma-bounded (1); Modules on Sites,
Tags 03EK, 03ER and 03EO.
(blueprint: lem-sf-strict-dvr-flat-tensor-sequence)

Proof: Write C_m for strictDvrFiniteCoefficient m and let T_m be the functor
C_m tensor -. Its value on P^j is canonically isomorphic to the restriction of
scalar extension along the completion projection. The isomorphism is induced by
the identity on the sectionwise scalar-first tensor product and normalized by the
sheafification unit. It is natural in the module variable, so it identifies the
complex obtained by applying T_m to P with unrestrictedTowerComplex m P.
Apply the bifunctorial sheaf tensor to the given coefficient injection and to the
quotient. Transport these natural transformations through the preceding isomorphisms,
and then apply mapHomologicalComplex to obtain chain maps. The injection has exactly
the stated formula by the normalization on all local pure tensors. The quotient
has formula s tensor x maps to q(s) tensor x; the uniqueness clause for the
published unrestrictedIntegralTransition identifies its chain map with the actual
unrestrictedTowerTransition. The composite is zero by functoriality and the given
coefficient zero equation. In degree j, the sequence is the given short exact
sequence mapped by - tensor P^j. IsFlatOnSite says this functor is exact; hence
its image is short exact. Transporting by the normalized isomorphisms preserves
short exactness and proves the asserted evaluated rows. This argument requires
only flatness of the terms, without K-flatness or any boundedness condition. -/
theorem strictDvrFlatTensorSequence
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hflat : ∀ j : ℤ, SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) (P.X j))
    (a : ∀ n : ℕ, strictDvrFiniteCoefficient l E X 0 ⟶
      strictDvrFiniteCoefficient l E X (n + 1))
    (hseq : ∀ n : ℕ, ∃ hz : a n ≫ strictDvrCoefficientQuotient l E X n = 0,
      (ShortComplex.mk (a n) (strictDvrCoefficientQuotient l E X n) hz).ShortExact) :
    ∃ (i : ∀ n : ℕ, unrestrictedTowerComplex l E X 0 P ⟶
        unrestrictedTowerComplex l E X (n + 1) P),
      (∀ (n : ℕ) (j : ℤ) (U : X.ProEtᵒᵖ)
        (s : (strictDvrFiniteCoefficient l E X 0).val.obj U)
        (x : (P.X j).val.obj U),
        ((i n).f j).val.app U (unrestrictedTowerTensorSection l E X 0 (P.X j) U s x) =
          unrestrictedTowerTensorSection l E X (n + 1) (P.X j) U
            ((a n).val.app U s) x) ∧
      ∀ n : ℕ, ∃ hz : i n ≫ unrestrictedTowerTransition l E X P n = 0,
        (∀ j : ℤ, ((ShortComplex.mk (i n) (unrestrictedTowerTransition l E X P n) hz).map
          (HomologicalComplex.eval (scalarReductionSource l E X) (.up ℤ) j)).ShortExact) := by
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      CommRingCat.{max u (t + 1)} := integralCoefficientRingSheafify.{t, u} X
  classical
  let i := fun n ↦ reductionMap l E X (a n) P
  have hz (n : ℕ) : i n ≫ unrestrictedTowerTransition l E X P n = 0 := by
    dsimp only [i]
    rw [← reductionMap_quotient, reductionMap_comp, (hseq n).choose, reductionMap_zero]
  refine ⟨i, ?_, fun n ↦ ⟨hz n, ?_⟩⟩
  · intro n j U s x
    exact (congrArg (fun f ↦ f.val.app U
      (unrestrictedTowerTensorSection l E X 0 (P.X j) U s x))
      (reductionMap_f l E X (a n) P j)).trans
        (reductionTensorMap_tmul l E X (a n) (P.X j) U s x)
  · intro j
    have ht : (reductionTensorMap l E X (a n)).app (P.X j) ≫
        (reductionTensorMap l E X (strictDvrCoefficientQuotient l E X n)).app
          (P.X j) = 0 := by
      rw [reductionTensorMap_comp, (hseq n).choose, reductionTensorMap_zero]
    let T := ShortComplex.mk ((reductionTensorMap l E X (a n)).app (P.X j))
      ((reductionTensorMap l E X (strictDvrCoefficientQuotient l E X n)).app (P.X j)) ht
    let S := (ShortComplex.mk (i n) (unrestrictedTowerTransition l E X P n) (hz n)).map
      (HomologicalComplex.eval (scalarReductionSource l E X) (.up ℤ) j)
    have e : T ≅ S := by
      refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · change 𝟙 _ ≫ (reductionMap l E X (a n) P).f j =
          (reductionTensorMap l E X (a n)).app (P.X j) ≫ 𝟙 _
        simpa only [Category.comp_id, Category.id_comp] using
          reductionMap_f l E X (a n) P j
      · change 𝟙 _ ≫ (unrestrictedTowerTransition l E X P n).f j =
          (reductionTensorMap l E X (strictDvrCoefficientQuotient l E X n)).app
            (P.X j) ≫ 𝟙 _
        simpa only [Category.comp_id, Category.id_comp] using
          ((congrArg (fun f ↦ f.f j) (reductionMap_quotient l E X n P)).symm.trans
            (reductionMap_f l E X (strictDvrCoefficientQuotient l E X n) P j))
    exact ShortComplex.shortExact_of_iso e
      (reductionTensorMap_shortExact l E X (a n) (strictDvrCoefficientQuotient l E X n)
        (hseq n).choose (hseq n).choose_spec (P.X j) (hflat j) ht)

end WeilConjectures
