/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Supporting.StrictDvrReductionTriangles
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedEpimorphicTopDerivedLimit
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackIdentity
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Cohomological bounds from complete residue Tor amplitude

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1) and (2);
sites-cohomology.tex, Tags 0942 and 0947; algebraization.tex, Tag 099I
(blueprint: lem-sf-complete-residue-cohomology-bounds).

The completion is the inverse limit of constant quotient ring sheaves, not the
constant sheaf of the valuation ring. Level zero of the reduction API means the
positive exponent one, hence the residue field. No characteristic, constructibility,
or local constancy condition is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

private instance (priority := 4000) boundsCoefficientLocallyBijective (Y : Scheme.{u}) :
    (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Y

private instance (priority := 4000) boundsSiteSmall (Y : Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{u} _

private theorem tor_cohomology_bounds
    (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleDerivedCategory Y A) (a b : ℤ)
    (hM : HasProEtaleTorAmplitude Y A M a b) (j : ℤ) (hj : j < a ∨ b < j) :
    IsZero ((DerivedCategory.homologyFunctor _ j).obj M) := by
  let R := proEtaleConstantRing Y A
  let C := proEtaleRingModules Y R
  let : MonoidalCategory C := SheafOfModules.monoidalCategory R
  let L := DerivedCategory.Q.objPreimage M
  let eL : DerivedCategory.Q.obj L ≅ M := DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral.{u + 1, u}
    (J := ProEt.topology Y) (R := R) L
  let : QuasiIso f := hf
  have hz := hM.2 L P ⟨eL⟩ f hf hP (MonoidalCategory.tensorUnit C) j hj
  let et : derivedTensor Y A L
      ((HomologicalComplex.single C (.up ℤ) 0).obj (MonoidalCategory.tensorUnit C))
      P f hf hP ≅ M :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ eL
  exact ((DerivedCategory.homologyFunctor C j).mapIso et).isZero_iff.mp hz

private theorem reduction_transition_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (D : FiniteFieldDatum) (hl : l ≠ D.p)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ) :
    integralTowerTransition l E X D hl P n = unrestrictedTowerTransition l E X P n := by
  have h := (integralTowerMaps_existUnique l E X D hl P).unique
    (integralTowerMaps_existUnique l E X D hl P).exists.choose_spec
    (y₂ := (unrestrictedTowerUnit l E X P, unrestrictedTowerTransition l E X P))
  apply congrArg (fun z ↦ z.2 n) (h ?_)
  constructor
  · exact unrestrictedTowerUnit_condition l E X P
  · intro m i U s x
    have ht := (unrestrictedIntegralTransition_existsUnique l E X m).exists.choose_spec
      P i U s x
    unfold unrestrictedIntegralTensorSection at ht
    unfold unrestrictedTowerTransition unrestrictedIntegralTransition integralTowerTensorSection
    exact ht

attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective in
/-- A derived-complete complex has the same cohomological bounds as a Tor interval
of its residue reduction, tested after restriction to every small-site object.

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1),(2);
sites-cohomology.tex, Tags 0942 and 0947; algebraization.tex, Tag 099I
(blueprint: lem-sf-complete-residue-cohomology-bounds).

Proof:
1. Test residue Tor amplitude with the coefficient sheaf itself on X. The tensor
unit identity gives vanishing of residue cohomology outside [a,b].
2. Choose one flat-term K-flat resolution P by lem-pc-kflat-resolution. By
lem-pur-derived-change-of-rings its reductions compute every K_n. Their actual
chain maps 1_P tensor (C_(n+1) to C_n) give the canonical quotient transitions.
3. The DVR coefficient sequence 0 to k_X to C_(n+1) to C_n to 0 is short exact:
the first map sends r to varpi^n r; cancellation proves injectivity and identifies
its image with the quotient kernel. Surjectivity and these identities pass to
constant sheaves locally. Compatibility of the limit projections makes the maps
B_X-linear (def-weil-l-adic-coefficient-extension, def-weil-pbc-constant-sheaf).
4. Flatness of each term of P preserves this exact sequence
(def-pc-flat-sheaf-modules). Apply lem-weil-pbc-complex-ses-triangle and
lem-sf-derived-homology-long-exact to obtain the cohomology exact sequences.
5. Induction gives cohomology in [a,b] for all K_n. The exact sequence in degree b
also makes each canonical transition on H^b epimorphic.
6. Apply proposition-milnor-sequence--2 to this strict tower. By proposition-exact-products--2,
its termwise product represents the product in D(Mod(B_X)), and localization
identifies 1-T with the tower transition endomorphism. Rotating the cone triangle
gives a Roos triangle (def-weil-abstract-derived-category,
def-weil-triangulated-category, def-weil-derived-limit). Completeness and the
uniqueness clause of lemma-reduction-derived-nakayama identify K up to isomorphism
with this Milnor middle term.
7. For j<a and j>b+1 both outer Milnor terms vanish. At j=b+1, the right term is
zero and proposition-milnor-sequence--3 kills R^1 lim H^b(K_n), since its transitions are
epimorphic. Exactness gives the asserted vanishing in every remaining degree. -/
theorem complete_residue_cohomology_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [CompactSpace X]
    (K : @DerivedCategory (integralTowerModules.{u, u} l E X) _
      (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
        (completedIntegralCoefficientSheafUnrestricted l E X)
        (integralCoefficientAbSheafify.{u, u} X)
        (integralCoefficientAbLocallyBijective.{u, u} X))
      (integralTowerHasDerivedCategory.{u, u} l E X))
    (_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback.{u} V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) a b) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((@DerivedCategory.homologyFunctor (integralTowerModules.{u, u} l E X) _
        (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
          (completedIntegralCoefficientSheafUnrestricted l E X)
          (integralCoefficientAbSheafify.{u, u} X)
          (integralCoefficientAbLocallyBijective.{u, u} X))
        (integralTowerHasDerivedCategory.{u, u} l E X) j).obj K) := by
  classical
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} X
  obtain ⟨D, hl, P₀, G, q, hq, e₀, hprod, δ₀, hlim⟩ := _hcomplete
  obtain ⟨P, e, hP, hflat, c, hc, i, hi, htri⟩ := strictDvrReductionTriangles.{u, u} l E X K
  have hres : ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E X) j).obj
        (strictDvrDerivedReduction l E X K 0)) := by
    let A := Padic.coefficientExtensionRing l E 1
    let : Finite A := Padic.finite_coefficientExtensionRing l E 1 (by omega)
    let M := (scalarReductionDerivedExtension l E X 0).obj K
    let V : X.ProEt := ProEt.mk (𝟙 X)
    obtain ⟨eR, _, _, eM, _, α, _, _, β, _, γ, _⟩ :=
      proEtaleDerivedPullback_identity X A
    let γ' : proEtaleRingDerivedPullback (𝟙 X)
        (proEtaleConstantRing X A) (proEtaleConstantRing X A)
        (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso
          (ULift.{u + 1, u} A) (𝟙 X)) ≅ 𝟭 _ := γ
    intro j hj
    have hz := tor_cohomology_bounds V.left A _ a b (_hTor V) j hj
    have hzM : IsZero ((DerivedCategory.homologyFunctor _ j).obj M) :=
      ((DerivedCategory.homologyFunctor _ j).mapIso (γ'.app M)).isZero_iff.mp hz
    exact ((scalarReductionRestriction l E X 0).map_isZero hzM).of_iso
      (((scalarReductionRestriction l E X 0).mapDerivedCategoryHomologyFunctorIso j).symm.app M)
  have hbounds : ∀ (n : ℕ) (j : ℤ), j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E X) j).obj
        (strictDvrDerivedReduction l E X K n)) := by
    intro n
    induction n with
    | zero => exact hres
    | succ n hn =>
      obtain ⟨hz, hex, δ, hT⟩ := htri n
      intro j hj
      exact (DerivedCategory.HomologySequence.exact₂ _ hT j).isZero_of_both_isZero
        (hres j hj) (hn j hj)
  have htop : ∀ n : ℕ, Epi
      ((DerivedCategory.homologyFunctor (scalarReductionSource l E X) b).map
        (strictDvrDerivedQuotientTransition l E X P hP e n)) := by
    intro n
    obtain ⟨hz, hex, δ, hT⟩ := htri n
    exact (DerivedCategory.HomologySequence.exact₃ _ hT b (b + 1) rfl).epi_f
      ((hres (b + 1) (Or.inr (by omega))).eq_zero_of_tgt _)
  let C := scalarReductionSource l E X
  let Q := DerivedCategory.Q (C := C)
  let H := DerivedCategory.homologyFunctor C
  obtain ⟨T, s, hs, t, hst⟩ := DerivedCategory.right_fac (e.hom ≫ e₀.inv)
  let : IsIso (Q.map s) := hs
  have ht : Q.map t = Q.map s ≫ e.hom ≫ e₀.inv := by
    rw [hst, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have : IsIso (Q.map t) := by rw [ht]; infer_instance
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hs
  have : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp inferInstance
  obtain ⟨S, r, hS, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := completedIntegralCommRingSheafUnrestricted l E X) T
  have : QuasiIso r := hr
  have hsr : CochainComplex.IsKFlatResolutionIndependentCoefficients.{u + 1, u, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l E X) (r ≫ s) :=
    ⟨inferInstance, hS⟩
  have htr : CochainComplex.IsKFlatResolutionIndependentCoefficients.{u + 1, u, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l E X) (r ≫ t) :=
    ⟨inferInstance, hS⟩
  let c (n : ℕ) :=
    (unrestrictedTowerComparison.{u, u} l E X n (r ≫ s) (𝟙 P) hsr
      ⟨inferInstance, hP⟩).symm ≪≫
      unrestrictedTowerComparison.{u, u} l E X n (r ≫ t) q htr hq
  have hct (n : ℕ) :
      Q.map (unrestrictedTowerTransition l E X P n) ≫ (c n).hom =
        (c (n + 1)).hom ≫ Q.map (integralTowerTransition l E X D hl P₀ n) := by
    have h₁ := (unrestrictedReductionTowerWellDefined.{u, u} l E X (r ≫ s) (𝟙 P)
      hsr ⟨inferInstance, hP⟩).2 n
    have h₂ := (unrestrictedReductionTowerWellDefined.{u, u} l E X (r ≫ t) q htr hq).2 n
    rw [reduction_transition_eq]
    dsimp only [c, Iso.trans_hom, Iso.symm_hom]
    apply (cancel_epi
      (unrestrictedTowerComparison.{u, u} l E X (n + 1) (r ≫ s) (𝟙 P)
        hsr ⟨inferInstance, hP⟩).hom).mp
    dsimp only [Q]
    simp only [← Category.assoc, ← h₁, Iso.hom_inv_id]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp] using h₂
  have hzP (n : ℕ) (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((H j).obj (Q.obj (unrestrictedTowerComplex l E X n P))) :=
    (hbounds n j hj).of_iso ((H j).mapIso (strictDvrReductionComparison l E X P hP e n))
  have heP (n : ℕ) : Epi ((H b).map
      (Q.map (unrestrictedTowerTransition l E X P n))) := by
    have := htop n
    have heq : (H b).map (Q.map (unrestrictedTowerTransition l E X P n)) =
        (H b).map (strictDvrReductionComparison l E X P hP e (n + 1)).hom ≫
          (H b).map (strictDvrDerivedQuotientTransition l E X P hP e n) ≫
            (H b).map (strictDvrReductionComparison l E X P hP e n).inv := by
      simp [strictDvrDerivedQuotientTransition, ← Functor.map_comp, Category.assoc, Q]
    rw [heq]
    infer_instance
  have hz₀ (n : ℕ) (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((integralTowerComplex l E X D hl n P₀).homology j) :=
    (hzP n j hj).of_iso
      (((DerivedCategory.homologyFunctorFactors C j).app
          (integralTowerComplex l E X D hl n P₀)).symm ≪≫ ((H j).mapIso (c n)).symm)
  have he₀ (n : ℕ) :
      Epi (HomologicalComplex.homologyMap (integralTowerTransition l E X D hl P₀ n) b) := by
    have := heP n
    have heq := congrArg ((H b).map) (hct n)
    simp only [Functor.map_comp] at heq
    have : Epi ((H b).map (Q.map (integralTowerTransition l E X D hl P₀ n))) := by
      have : Epi ((H b).map (c (n + 1)).hom ≫
          (H b).map (Q.map (integralTowerTransition l E X D hl P₀ n))) := by
        rw [← heq]
        infer_instance
      exact epi_of_epi ((H b).map (c (n + 1)).hom) _
    have : Epi ((H b).map (Q.map (integralTowerTransition l E X D hl P₀ n)) ≫
        (DerivedCategory.homologyFunctorFactors C b).hom.app
          (integralTowerComplex l E X D hl n P₀)) := inferInstance
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality] at this
    exact epi_of_epi
      ((DerivedCategory.homologyFunctorFactors C b).hom.app
        (integralTowerComplex l E X D hl (n + 1) P₀)) _
  let : HasProduct (fun n : ℕ ↦ Q.obj (integralTowerComplex l E X D hl n P₀)) := hprod
  have hL : IsDerivedLimit
      (K := fun n : ℕ ↦ Q.obj (integralTowerComplex l E X D hl n P₀))
      (fun n : ℕ ↦ Q.map (integralTowerTransition l E X D hl P₀ n)) K := by
    refine ⟨Pi.lift (fun n ↦
      ((integralReductionTowerCone l E X D hl q hq).extend e₀.inv).π.app
        (Opposite.op n)), δ₀, ?_⟩
    have htower :
        (fun n : ℕ ↦ (integralReductionTower l E X D hl P₀).map
          (homOfLE n.le_succ).op) =
        (fun n : ℕ ↦ Q.map (integralTowerTransition l E X D hl P₀ n)) := by
      funext n
      exact Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [htower] at hlim
    exact hlim
  exact ProEt.bounded_epimorphic_top_derivedLimit.{u, u} X
    (completedIntegralCoefficientSheafUnrestricted l E X)
    (completedIntegralCoefficient_mul_commUnrestricted l E X)
    (fun n ↦ integralTowerComplex l E X D hl n P₀)
    (fun n ↦ integralTowerTransition l E X D hl P₀ n) K hL a b _hab hz₀ he₀

end WeilConjectures
