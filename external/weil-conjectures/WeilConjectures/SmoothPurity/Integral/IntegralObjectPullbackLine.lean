/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
public import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.SmoothPurity.ConstantScalarUnitQuasiIsomorphism.ConstantScalarUnitQuasiIsomorphism
import WeilConjectures.SmoothPurity.Integral.IntegralObjectPullbackQuotientBasis

/-! # Completed inverse image on a trivialized integral line

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9;
Stacks Project, Tags 04J0, 06YY and 08TC.
(blueprint: lem-pur-integral-object-pullback-line).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open Opposite
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private noncomputable instance (priority := 5000) fixedAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T

private noncomputable instance (priority := 5000) fixedAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

private noncomputable instance (priority := 5000) fixedSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

private theorem existsCoefficientTestDatum (l : ℕ) :
    ∃ D : FiniteFieldDatum.{0}, l ≠ D.p := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  refine ⟨D, ?_⟩
  change l ≠ p
  omega

/-- A slice basis computes the actual completed inverse image of a line.

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9;
Stacks Project, Tags 04J0, 06YY and 08TC.
(blueprint: lem-pur-integral-object-pullback-line).

Proof: place L in degree zero. Local freeness makes this a K-flat complex with
flat terms, so it is an allowed representative of integralDerivedPullback. At
quotient exponent n+1, ordinary scalar extension commutes with restriction to
W. Extend the supplied slice basis to the finite quotient. Inverse image along
the object W is slice restriction followed by the pro-etale slice equivalence;
the unit-normalized constant-ring comparison then identifies the pulled-back
finite line with the regular finite coefficient module on W.left. The basis
is the reduction of one fixed integral basis, so these identifications commute
with every quotient transition and with the augmentation. Consequently the
whole strict pullback tower is isomorphic to the coefficient quotient tower
placed in degree zero. Products and the mapping-cocone construction carry this
tower isomorphism to a Roos-complex isomorphism. The regular completed module
is derived complete: its ordinary quotient tower has the completed coefficient
ring as its limit and locally surjective transitions. Its augmented Roos map
is therefore an isomorphism after Q. Compose the defining representative
comparison of integralDerivedPullback, the Roos isomorphism, and the inverse
regular augmentation. This proves exactly the displayed object isomorphism,
including the empty scheme and the zero module category. -/
theorem integralObjectPullbackLine (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (W : X.ProEt)
    (L : integralTowerModules l E X) (hL : L.IsFiniteLocallyFreeOfRank 1)
    (e : L.over W ≅
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X)).over W) :
    Nonempty ((integralDerivedPullback l E W.hom).obj
      ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W.left))) := by
  classical
  let _ := hL
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let : HasDerivedCategory (SheafOfModules.LineUnbounded.Modules.{u, u} X R) :=
    HasDerivedCategory.standard _
  let P := (CochainComplex.singleFunctor (integralTowerModules l E X) 0).obj L
  let Rm : Sheaf (ProEt.topology X) RingCat.{u + 1} :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  have hcover : ∀ U : X.ProEt, ∃ s : Sieve U,
      s ∈ AlgebraicGeometry.Scheme.ProEt.topology X U ∧
      ∀ (V : X.ProEt) (f : V ⟶ U), s f →
        Nonempty (L.over V ≅ SheafOfModules.unit (Rm.over V)) := by
    obtain ⟨I, V, hV, h⟩ :=
      (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
        (M := L) (r := 1)).mp inferInstance
    intro U
    refine ⟨Sieve.ofObjects V U, hV U, ?_⟩
    rintro Z f ⟨i, ⟨g⟩⟩
    let e : L.over (V i) ≅ SheafOfModules.unit (Rm.over (V i)) :=
      (h i).some ≪≫ SheafOfModules.freeUniqueIso (ULift (Fin 1))
    exact ⟨((SheafOfModules.overFunctorMap Rm g).app L).symm ≪≫
      (SheafOfModules.overMap Rm g).mapIso e ≪≫
        SheafOfModules.overMapUnitIso (R := Rm) g⟩
  obtain ⟨_, _, _, _, _, _, _, hflat, _⟩ :=
    SheafOfModules.LineEvaluation.evaluation_inverse_pair.{u + 1, u, u + 1} R L hcover
  obtain ⟨hP, hf, _⟩ :=
    SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization R L hflat
  let Pg : (integralOperationsGoodComplex l E X).FullSubcategory := ⟨P, hP, hf⟩
  let F := (integralOperationsPullbackTowerFunctor l E W.hom).obj P
  let O := ConstantScalarStrictUnit.regularComplex l E W.left
  let G := (integralScalarTowerFunctor l E E (AlgHom.id _ _) W.left).obj O
  obtain ⟨b, hb⟩ := integralObjectPullbackQuotientBasis l E X W L e
  let a : F ≅ G := NatIso.ofComponents (fun n ↦ b n.unop) (by
    have hn := (NatTrans.ofOpSequence (F := F) (G := G) (fun n ↦ (b n).hom)
      (by
        intro n
        simpa only [F, G, integralOperationsPullbackTowerFunctor,
          integralScalarTowerFunctor, Functor.flip_obj_map,
          Functor.ofOpSequence_map_homOfLE_succ]
          using hb n)).naturality
    exact hn)
  obtain ⟨D, hl⟩ := existsCoefficientTestDatum l
  obtain ⟨_, _, _, _, ⟨η, hη, _⟩, _⟩ :=
    ConstantScalarStrictUnit.regular_scalar_strict_unit l E W.left E (AlgHom.id _ _) D hl
  obtain ⟨_, _, _, _, _, _, ⟨c, _, _⟩, _⟩ :=
    ConstantScalarUnitQuasiIsomorphism.regular_scalar_unit_quasi_isomorphism
      l E E (AlgHom.id _ _) W.left D hl η hη
  let d := (integralDerivedPullbackComparison l E W.hom).app Pg
  refine ⟨(integralDerivedPullback l E W.hom).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app L) ≪≫ d ≪≫
    DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso a) ≪≫ c ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
      (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E W.left))).symm⟩

end WeilConjectures
