/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
public import Mathlib.CategoryTheory.Triangulated.Subcategory

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingEndpointScalarRestrictions
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingCanonicalScalarInvertibility
import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

/-! # Scalar mates for already realized ring operations

This statement concerns scalar restriction and its counit mates. The operations,
ambient left realizations, and their shift compatibility are supplied as inputs.
Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
  AlgebraicGeometry.Scheme.completedAdicChange AlgebraicGeometry.Scheme.reductionChange
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.presheafToSheaf
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private def ringFullyFaithful (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
    (RingStage.inclusion.{u, v} l Ω T s).FullyFaithful :=
  match s with
  | .finite E n => (finiteTorConstructible l E.carrier n n.pos T).fullyFaithfulι
  | .integral E => (finiteTorConstructibleIntegral l E.carrier T).fullyFaithfulι

private theorem liftNaturalIso
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {F G : C₀ ⥤ C₁} {I : C₁ ⥤ C₂} (fully : I.FullyFaithful)
    (z : F ⋙ I ≅ G ⋙ I) :
    ∃ d : F ≅ G, ∀ K, I.map (d.hom.app K) = z.hom.app K := by
  let d : F ≅ G := NatIso.ofComponents
    (fun K ↦ fully.preimageIso (z.app K)) (fun f ↦ by
      apply fully.map_injective
      simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
        Iso.app_hom, fully.map_preimage]
      exact z.hom.naturality f)
  exact ⟨d, fun K ↦ fully.map_preimage (z.hom.app K)⟩

attribute [local instance] constructionInclusionShift

private theorem commShift_of_whiskerRight
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {F G : C₀ ⥤ C₁} {I : C₁ ⥤ C₂} [I.Faithful]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] [I.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift (whiskerRight τ I) ℤ] :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  ext X
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso n).hom.app (G.obj X))).mp
  have ht := NatTrans.shift_app_comm (whiskerRight τ I) n X
  simpa only [Functor.commShiftIso_comp_hom_app, whiskerRight_app,
    NatTrans.comp_app, whiskerLeft_app, Functor.map_comp, Category.assoc,
    ← Functor.commShiftIso_hom_naturality] using ht

set_option linter.flexible false in
private theorem scalarComparison
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {s t : RingStage.{max u v} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a)
    (A : Operation.{u, v} l Ω X Y (s.stage l))
    (B : Operation.{u, v} l Ω X Y (t.stage l))
    (rA : LeftRealization.{u, v} l Ω c s A)
    (rB : LeftRealization.{u, v} l Ω c t B)
    (SX : Scalar.{u, v} l Ω a X) (SY : Scalar.{u, v} l Ω a Y)
    (hA : rA.hom.CommShift ℤ) (hB : rB.hom.CommShift ℤ)
    (hSX : SX.realization.hom.CommShift ℤ) (hSY : SY.realization.hom.CommShift ℤ) :
    ∃ d : CounitComparison.{u, v} l Ω A B SX.functor SY.functor,
      CounitQNormalized.{u, v} l Ω c a SX SY rA rB d := by
  classical
  let IX := RingStage.inclusion.{u, v} l Ω X s
  let IY := RingStage.inclusion.{u, v} l Ω Y t
  letI := hA
  letI := hB
  letI := hSX
  letI := hSY
  letI := PurCompactSupport.comparison_commShift a c
  obtain ⟨hcomp, hmate⟩ :=
    ring_canonical_scalar_invertibility.{u, v} l Ω D hl f c a ha A B rA rB SX SY
  letI := hcomp
  let e : (A.F ⋙ SY.functor) ⋙ IY ≅ (SX.functor ⋙ B.F) ⋙ IY :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft A.F SY.realization ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight rA (pbcDerivedExtend (a.map Y)) ≪≫
      Functor.associator _ _ _ ≪≫ asIso (whiskerLeft IX (PurCompactSupport.comparison a c)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight SX.realization.symm (PurCompactSupport.image (t.coefficients l) c) ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft SX.functor rB.symm ≪≫
      (Functor.associator _ _ _).symm
  obtain ⟨q, hqapp⟩ := liftNaturalIso (ringFullyFaithful.{u, v} l Ω Y t) e
  have hq : whiskerRight q.hom IY = e.hom := by
    ext K
    exact hqapp K
  have hnorm (K : C.{u, v} l Ω X (s.stage l)) :
      IY.map (q.hom.app K) ≫ rB.hom.app (SX.functor.obj K) ≫
        (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
      SY.realization.hom.app (A.F.obj K) ≫
        (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
        (PurCompactSupport.comparison a c).app (IX.obj K) := by
    rw [hqapp K]
    suffices hunit :
        (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
          (PurCompactSupport.comparison a c).app (IX.obj K) ≫
            𝟙 ((PurCompactSupport.image (t.coefficients l) c).obj
              ((pbcDerivedExtend (a.map X)).obj (IX.obj K))) =
        (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
          (PurCompactSupport.comparison a c).app (IX.obj K) by
      simp [e, Category.assoc, ← Functor.map_comp]
      exact hunit
    erw [Category.comp_id]
  have heShift : e.hom.CommShift ℤ := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, asIso_hom]
    infer_instance
  have hqShift : q.hom.CommShift ℤ := by
    letI : IY.Faithful := (ringFullyFaithful.{u, v} l Ω Y t).faithful
    haveI : (whiskerRight q.hom IY).CommShift ℤ := by rw [hq]; exact heShift
    exact commShift_of_whiskerRight (I := IY) q.hom
  let beta := (mateEquiv A.adjunction B.adjunction q.inv)
  letI : IsIso beta := hmate q hnorm
  letI := hqShift
  letI : A.adjunction.CommShift ℤ := ⟨A.unitShift, A.counitShift⟩
  letI : B.adjunction.CommShift ℤ := ⟨B.unitShift, B.counitShift⟩
  have hbShift : beta.CommShift ℤ := by
    change NatTrans.CommShift
      ((A.G ⋙ SX.functor).rightUnitor.inv ≫
        whiskerLeft (A.G ⋙ SX.functor) B.adjunction.unit ≫
        (Functor.associator A.G SX.functor (B.F ⋙ B.G)).hom ≫
        whiskerLeft A.G (Functor.associator SX.functor B.F B.G).inv ≫
        whiskerLeft A.G (whiskerRight q.inv B.G) ≫
        whiskerLeft A.G (Functor.associator A.F SY.functor B.G).hom ≫
        (Functor.associator A.G A.F (SY.functor ⋙ B.G)).inv ≫
        whiskerRight A.adjunction.counit (SY.functor ⋙ B.G) ≫
        (SY.functor ⋙ B.G).leftUnitor.hom) ℤ
    infer_instance
  refine ⟨⟨q, asIso beta, ?_, hqShift, hbShift⟩, hnorm⟩
  intro L
  have hc := mateEquiv_counit A.adjunction B.adjunction q.inv L
  change B.F.map (beta.app L) ≫ B.adjunction.counit.app (SY.functor.obj L) = _ at hc
  change q.hom.app (A.G.obj L) ≫ B.F.map (beta.app L) ≫
    B.adjunction.counit.app (SY.functor.obj L) = _
  rw [hc]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem endpointRestrictions
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p) (X Y : Scheme.{max u v})
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (side : Bool) :
    ∃ scalar : ∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)),
      Allowed l a → Scalar.{u, v} l Ω a (endpoint X Y side),
    ∃ finiteScalar_eq : ∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).functor ⋙ RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (.finite E n) =
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) s ⋙
          pbcDerivedExtend (a.map (endpoint X Y side)),
    (∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).realization = eqToIso (finiteScalar_eq E n a ha)) ∧
    (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier),
      (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).functor ⋙
          RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (.integral L) =
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (.integral E) ⋙
          integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side)) ∧
    (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u, v} l Ω (endpoint X Y side) (.integral E)),
      HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).realization.inv.app K)
        ((completedScalarComparison l E.carrier L.carrier i (endpoint X Y side)).app K.obj)) ∧
    (∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a), (scalar a ha).realization.hom.CommShift ℤ) ∧
    (∀ {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a),
      Nonempty (ScalarIdentity.{u, v} l Ω h (endpoint X Y side) (scalar a ha))) := by
  cases side
  · dsimp only [endpoint]
    exact exists_ring_endpoint_scalar_restrictions.{u, v} l Ω D hl Y
  · dsimp only [endpoint]
    exact exists_ring_endpoint_scalar_restrictions.{u, v} l Ω D hl X

/-- Scalar mates for supplied, ambient-realized adjunctions.
Source: Zheng, Lemma 5.22, Construction 5.25, Propositions 5.24 and 5.26;
coefficient construction steps 2 and 4
(blueprint: lem-sf-ring-scalar-mates-for-realized-operations).

Proof:
1. At each endpoint restrict ambient finite-target derived extension to the full
finite-Tor subcategory. Flat representatives show preservation of its Tor interval;
finite scalar constructibility gives constructible cohomology. Use the literal lift
and equality realization. For completed extension use the published strict-tower
scalar functor, realized by the inverse finite-free completed scalar comparison.
Its reductions preserve the common bounds. Make these choices at the endpoints,
independently of compactification.
2. At each compactification take the finite transported adjunctions and reconstruct
the normalized system adjunction integrally using the reduction/total-limit
equivalence and the proper/open system realization. Compare their left functors with the
supplied operations by lifting the composite of their ambient realizations through
the full inclusion. Right-adjoint uniqueness gives the corresponding right isomorphism
preserving units and counits. Adjoint shift uniqueness and the left realization shift
show that these changes of presentation preserve shifts.
3. Apply finite scalar mates to finite generators. For integral reduction use the
system evaluation isomorphisms with their units and counits. For completed extension
use the finite-free system comparison and cofinal recovery of the ramified subsequence,
then take total limit. Construct q intrinsically from system proper scalar
projection and open tensor maps, and define b as its system counit transpose.
The actual system unit/counit comparison identifies their evaluations with the
finite mates. Their cones therefore have zero evaluations, so both are invertible.
Reconstruction transports their counit equation by its transpose formula. The
simultaneous proper/open realization identifies q with the canonical ambient
coefficient mate. These are identities of system maps before limit, without
assuming that evaluations are faithful on morphisms.
4. Conjugate q and b by the isomorphisms of step 2 and the unique endpoint scalar
realization isomorphisms. Naturality and the adjunction equations preserve the counit
transpose equation. Whiskering, inversion and composition preserve shifts. The ambient
proper/open mate gives exactly CounitQNormalized for the supplied left realizations.
5. Lift the ambient multiplication tensor unitor, preceded by the given equality of
coefficient maps, through the fully faithful endpoint inclusion. Its map/preimage
equation proves the displayed ScalarIdentity normalization for every actual identity
coefficient map, including composite Allowed witnesses.
6. Induct on Allowed witnesses. Identities use multiplication tensor unitors; composites
use balanced tensor associators. Proper/open mate pasting identifies the resulting q
with the canonical map for the actual composite coefficient map. Transposition gives
its counit equation. Compositions of the generator isomorphisms remain invertible.
Full inclusion retains the same endpoint scalar restrictions for all compactifications.
Empty schemes use zero objects; positive levels include the residue level, and nonflat
quotients use derived extension. No operation, adjunction or scalar associator is
constructed here. -/
theorem exists_ring_scalar_mates (D : FiniteFieldDatum.{max u v}) (_hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (operation : ∀ (c : Compactification f) (s : RingStage.{max u v} l),
      Operation.{u, v} l Ω X Y (s.stage l))
    (left : ∀ (c : Compactification f) (s : RingStage.{max u v} l),
      LeftRealization.{u, v} l Ω c s (operation c s))
    (_leftShift : ∀ (c : Compactification f) (s : RingStage.{max u v} l),
      letI : (RingStage.inclusion.{u, v} l Ω X s).CommShift ℤ :=
        match s with
        | .finite E n => @ObjectProperty.commShiftι _ _
            (finiteTorConstructible l E.carrier n n.pos X) ℤ _ _
            (finiteTriangulated l E n X).toIsStableUnderShift
        | .integral E => @ObjectProperty.commShiftι _ _
            (finiteTorConstructibleIntegral l E.carrier X) ℤ _ _
            (integralTriangulated l E X).toIsStableUnderShift
      letI : (RingStage.inclusion.{u, v} l Ω Y s).CommShift ℤ :=
        match s with
        | .finite E n => @ObjectProperty.commShiftι _ _
            (finiteTorConstructible l E.carrier n n.pos Y) ℤ _ _
            (finiteTriangulated l E n Y).toIsStableUnderShift
        | .integral E => @ObjectProperty.commShiftι _ _
            (finiteTorConstructibleIntegral l E.carrier Y) ℤ _ _
            (integralTriangulated l E Y).toIsStableUnderShift
      (left c s).hom.CommShift ℤ) :
    ∃ scalar : ∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool),
    Scalar.{u, v} l Ω a (endpoint X Y side),
    ∃ finiteScalar_eq : ∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool),
    (scalar (s := s) (t := .finite E n) a ha side).functor ⋙
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.finite E n) =
      RingStage.inclusion.{u, v} l Ω (endpoint X Y side) s ⋙
        pbcDerivedExtend (a.map (endpoint X Y side)),
    (∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool),
    (scalar (s := s) (t := .finite E n) a ha side).realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha side)) ∧
    (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool),
    (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).functor ⋙
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.integral L) =
      RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side)) ∧
    (∀ (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (side : Bool)
      (K : C.{u, v} l Ω (endpoint X Y side) (.integral E)),
    HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i (endpoint X Y side)).app K.obj)) ∧
    ∃ identityData : ∀ {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a) (side : Bool),
    ScalarIdentity.{u, v} l Ω h (endpoint X Y side) (scalar a ha side),
    ∃ comparison : ∀ (c : Compactification f) {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a),
    CounitComparison.{u, v} l Ω (operation c s) (operation c t)
      (scalar a ha true).functor (scalar a ha false).functor,
    ∀ (c : Compactification f) {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a),
    CounitQNormalized.{u, v} l Ω c a (scalar a ha true) (scalar a ha false)
      (left c s) (left c t) (comparison c a ha) := by
  classical
  choose scalar finite_eq hfinite hintegral hintegral_norm hshift hid using
    endpointRestrictions.{u, v} l Ω D _hl X Y
  let scalar' {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) := scalar side a ha
  let finite_eq' {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :=
    finite_eq side E n a ha
  have hc (c : Compactification f) {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
      ∃ d : CounitComparison.{u, v} l Ω (operation c s) (operation c t)
        (scalar' a ha true).functor (scalar' a ha false).functor,
        CounitQNormalized.{u, v} l Ω c a (scalar' a ha true) (scalar' a ha false)
          (left c s) (left c t) d :=
    scalarComparison.{u, v} l Ω D _hl f c a ha (operation c s) (operation c t)
      (left c s) (left c t) (scalar' a ha true) (scalar' a ha false)
      (_leftShift c s) (_leftShift c t) (hshift true a ha) (hshift false a ha)
  refine ⟨scalar', finite_eq', ?_, ?_, ?_, ?_⟩
  · intro s E n a ha side
    exact hfinite side E n a ha
  · intro E L i side
    exact hintegral side E L i
  · intro E L i side K
    exact hintegral_norm side E L i K
  · refine ⟨(fun {s} a h ha side ↦
      (hid side a h ha).some),
      (fun c {s t} a ha ↦ (hc c a ha).choose), ?_⟩
    exact fun c {s t} a ha ↦ (hc c a ha).choose_spec

end WeilConjectures.ConstructibleExceptionalCoefficients
