/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismTransport
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalAutomorphismScalarCoherence
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import WeilConjectures.AlgebraicGeometry.FibreDimension
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Completed coefficient transport and Weil categories

Source: Weil conjectures blueprint, finite coefficient and Weil-category definitions
(blueprint: def-wf-weil-category).

The finite coefficient stages use `pbcStageDatum` and `pbcStageUniformizer`:
these are the valuation-ring data transported along `Shrink.algEquiv`, with the
actual field inclusions conjugated by that canonical equivalence.

## Main definitions

- `WeilD`: fixed pairs for the geometric Frobenius pullback.
- `weilScalarExtension`: the coefficient transition with its Weil structure.
- `WeilDQbar`: the common-stage category of the finite Weil categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local irreducible] ScalarLocalization.category ScalarLocalization.preadditive
  ScalarLocalization.composition ScalarLocalization.linear ScalarLocalization.linearOriginal
  AlgebraicGeometry.Scheme.pbcIntegralLinear AlgebraicGeometry.Scheme.pbcCompletedDerivedLinear
  AlgebraicGeometry.Scheme.pbcCompletedModulesLinear
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer AlgebraicGeometry.Scheme.pbcScalarExtension
  AlgebraicGeometry.Scheme.pbcScalarAssociator
  AlgebraicGeometry.Scheme.pbcIsoRationalScalarComparison
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.pbcUniformizer
  AlgebraicGeometry.Scheme.pbcCompletedScalarSections
  AlgebraicGeometry.Scheme.pbcCompletedSection AlgebraicGeometry.Scheme.pbcCompletedScalar

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v z
variable {C : Type z} [Category.{v} C] [Preadditive C] (F : C ⥤ C) [F.Additive]

/-- The group laws on commuting Weil morphisms are inherited from the coefficient category.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def PreadditiveNormalized (P : Preadditive (IsoAlgebra F)) : Prop := by
  letI := P
  exact ∀ (K L : IsoAlgebra F) (f g : K ⟶ L),
    (f + g).hom.f = f.hom.f + g.hom.f ∧ (0 : K ⟶ L).hom.f = 0

/-- Commuting morphisms have the unique inherited preadditive structure.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: the commuting equation is closed under sums, negatives and zero because
F is additive. These operations make each commuting Hom set an additive
subgroup of the ambient Hom group. Bilinearity follows from ambient bilinearity.
Forgetting the structure is injective on each Hom set, so the displayed
equations determine the group operations and the preadditive structure uniquely. -/
theorem preadditive_exists :
    ∃! P : Preadditive (IsoAlgebra F), PreadditiveNormalized F P := by
  let P : Preadditive (IsoAlgebra F) :=
    inferInstanceAs (Preadditive (Algebra.IsIsoStr F).FullSubcategory)
  refine ⟨P, ?_, ?_⟩
  · intro K L f g
    exact ⟨rfl, rfl⟩
  · intro Q hQ
    apply Preadditive.ext
    funext K L
    apply AddCommGroup.ext
    funext f g
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    exact (hQ K L f g).1

/-- The group structure with its specified faithful underlying morphisms.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
instance preadditive : Preadditive (IsoAlgebra F) := (preadditive_exists F).exists.choose

section Cocycle
universe w v' z'
variable {I : Type w} [Preorder I] {A : I → Type z'} [∀ i, Category.{v'} (A i)]

set_option backward.isDefEq.respectTransparency false in
private theorem normalized_cocycle (S : StageSystem A) (P : ∀ i, A i ⥤ A i)
    (e : ∀ {i j} (h : i ≤ j), S.T h ⋙ P j ≅ P i ⋙ S.T h)
    (a : ∀ {i j k} (h : i ≤ j) (k : j ≤ k),
      mapOfNatIso (e h) ⋙ mapOfNatIso (e k) ≅ mapOfNatIso (e (h.trans k)))
    (ha : ∀ {i j k} (h : i ≤ j) (k : j ≤ k) (K : IsoAlgebra (P i)),
      ((a h k).hom.app K).hom.f = (S.assoc h k).hom.app K.carrier)
    {i j k l : I} (h : i ≤ j) (g : j ≤ k) (f : k ≤ l) (K : IsoAlgebra (P i)) :
    (mapOfNatIso (e f)).map ((a h g).hom.app K) ≫ (a (h.trans g) f).hom.app K =
      (a g f).hom.app ((mapOfNatIso (e h)).obj K) ≫ (a h (g.trans f)).hom.app K := by
  apply ObjectProperty.hom_ext
  apply Algebra.Hom.ext
  change (S.T f).map ((a h g).hom.app K).hom.f ≫
      ((a (h.trans g) f).hom.app K).hom.f =
    ((a g f).hom.app ((mapOfNatIso (e h)).obj K)).hom.f ≫
      ((a h (g.trans f)).hom.app K).hom.f
  rw [ha, ha, ha, ha]
  exact S.cocycle h g f K.carrier

/-- Lift the scalar associator using its compatibility with the endofunctors. -/
private theorem normalized_associator_exists (S : StageSystem A) (P : ∀ i, A i ⥤ A i)
    (e : ∀ {i j} (h : i ≤ j), S.T h ⋙ P j ≅ P i ⋙ S.T h)
    {i j k : I} (h : i ≤ j) (g : j ≤ k)
    (hc : ∀ K : A i,
      (P k).map ((S.assoc h g).hom.app K) ≫ (e (h.trans g)).hom.app K =
        (e g).hom.app ((S.T h).obj K) ≫ (S.T g).map ((e h).hom.app K) ≫
          (S.assoc h g).hom.app ((P i).obj K)) :
    ∃! a : mapOfNatIso (e h) ⋙ mapOfNatIso (e g) ≅ mapOfNatIso (e (h.trans g)),
      ∀ K : IsoAlgebra (P i), (a.hom.app K).hom.f = (S.assoc h g).hom.app K.carrier := by
  let a : mapOfNatIso (e h) ⋙ mapOfNatIso (e g) ≅ mapOfNatIso (e (h.trans g)) :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
      (Algebra.isoMk ((S.assoc h g).app K.carrier) (by
        change (P k).map ((S.assoc h g).hom.app K.carrier) ≫
            ((e (h.trans g)).hom.app K.carrier ≫ (S.T (h.trans g)).map K.obj.str) =
          ((e g).hom.app ((S.T h).obj K.carrier) ≫
            (S.T g).map ((e h).hom.app K.carrier ≫ (S.T h).map K.obj.str)) ≫
              (S.assoc h g).hom.app K.carrier
        rw [← Category.assoc, hc]
        simp only [Functor.map_comp, Category.assoc]
        have hn := (S.assoc h g).hom.naturality K.obj.str
        dsimp only [Functor.comp_map] at hn
        rw [hn]))) (by
          intro K L f
          apply ObjectProperty.hom_ext
          apply Algebra.Hom.ext
          exact (S.assoc h g).hom.naturality f.hom.f)
  refine ⟨a, fun _ ↦ rfl, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  apply Algebra.Hom.ext
  exact hb K

end Cocycle

section AdditiveTransport
variable {D' : Type*} [Category D'] [Preadditive D']
  {G : D' ⥤ D'} [G.Additive] {L : C ⥤ D'} [L.Additive]

end AdditiveTransport

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra
universe v z
variable {C : Type z} [Category.{v} C] {F : C ⥤ C}
end CategoryTheory.Endofunctor.IsoAlgebra

namespace WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.Scheme

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [hsep : IsSeparated X₀.hom] [hft : LocallyOfFiniteType X₀.hom]
  [hqc : QuasiCompact X₀.hom]

include hsep hft hqc

/-- The inherited base hypotheses needed by the PBC coefficient stages.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: finite type over a field is noetherian and finite-dimensional, also after
extension to the algebraic closure. The residue characteristic is D.p, and the
coefficient prime differs from it, so that prime is a unit in every local ring. -/
theorem weilGeometricFiber_coefficientHypotheses :
    IsNoetherian (D.geometricFiber X₀).left ∧
      (∃ m : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ m) ∧
      ∀ t : (D.geometricFiber X₀).left,
        IsUnit (c.l : (D.geometricFiber X₀).left.presheaf.stalk t) := by
  classical
  have := hsep
  let f := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let X := pullback X₀.hom f
  have : LocallyOfFiniteType (pullback.snd X₀.hom f) := inferInstance
  have : QuasiCompact (pullback.snd X₀.hom f) := inferInstance
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd X₀.hom f)
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd X₀.hom f)
  have hn : IsNoetherian X := {}
  change IsNoetherian X ∧ (∃ m : ℕ, topologicalKrullDim X ≤ m) ∧
    ∀ t : X, IsUnit (c.l : X.presheaf.stalk t)
  refine ⟨hn, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le_of_isPullback_of_compactSpace X₀.hom
    exact ⟨n, hn D.k f (pullback.fst X₀.hom f) (pullback.snd X₀.hom f)
      (IsPullback.of_hasPullback _ _)⟩
  · let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have hunit : IsUnit (c.l : D.k₀) :=
      isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k₀
        (Fact.out : c.l.Prime) c.different.symm)
    intro t
    simpa only [map_natCast] using hunit.map
      ((((Scheme.ΓSpecIso (.of D.k₀)).inv ≫
        (pullback.fst X₀.hom f ≫ X₀.hom).appTop) ≫
        X.presheaf.germ (⊤ : X.Opens) t (by trivial)).hom)

/-- The noetherian instance is a property of the specified geometric fiber.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: base change preserves finite type over the field; a finite-type scheme
over a noetherian field is noetherian. -/
@[instance] theorem weilGeometricFiber_isNoetherian :
    IsNoetherian (D.geometricFiber X₀).left := by
  have := hsep
  let f := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let X : Scheme.{u} := pullback X₀.hom f
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd X₀.hom f)
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd X₀.hom f)
  change IsNoetherian X
  exact {}

/-- The geometric-Frobenius pullback on the exact PBC rational coefficient category.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilFrobeniusPullback (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    PbcRationalCategory (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E) ⥤
      PbcRationalCategory (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E) :=
  pbcRationalIsoPullback (D.geometricFrobenius X₀)
    (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Weil complexes are fixed pairs in the raw rationalized PBC coefficient category.
The existing IsoAlgebra category has exactly the pairs (K, phi:P(K)≅K) and all
maps u with phi_K ≫ u = P(u) ≫ phi_L. Its identities and composites are those
of the coefficient category; the strict version has these same objects and maps.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
abbrev WeilD (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  CategoryTheory.Endofunctor.IsoAlgebra (weilFrobeniusPullback D c X₀ E)

/-- The underlying coefficient extension, using the geometric fiber's inherited hypotheses.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilCoefficientExtension {E F : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) :
    PbcRationalCategory (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E) ⥤
      PbcRationalCategory (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar F) (pbcStageUniformizer.{u} c.l c.Qbar F) :=
  pbcScalarExtension c.l c.Qbar (D.geometricFiber X₀).left
    (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
    (weilGeometricFiber_coefficientHypotheses D c X₀).2.2 h

/-- The canonical Frobenius/scalar comparison on the raw coefficient stages.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilFrobeniusScalarComparison {E F : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) :
    weilCoefficientExtension D c X₀ h ⋙ weilFrobeniusPullback D c X₀ F ≅
      weilFrobeniusPullback D c X₀ E ⋙ weilCoefficientExtension D c X₀ h :=
  pbcIsoRationalScalarComparison c.l c.Qbar (D.geometricFrobenius X₀)
    (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
    (weilGeometricFiber_coefficientHypotheses D c X₀).2.2 h

/-- Extension sends (K,phi) to (T K,c_K followed by T(phi)), with the same action
T on the underlying commuting morphisms.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilScalarExtension {E F : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) : WeilD D c X₀ E ⥤ WeilD D c X₀ F :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (F := weilFrobeniusPullback D c X₀ E) (G := weilFrobeniusPullback D c X₀ F)
    (L := weilCoefficientExtension D c X₀ h) (weilFrobeniusScalarComparison D c X₀ h)

/-- The tensor associator is Frobenius-equivariant and thus lifts uniquely to
Weil pairs. Its underlying map is specified, so it is not an arbitrary isomorphism.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: the scalar and Frobenius comparisons are mates of the sectionwise
identity restrictions. Composing these right-adjoint identities in either order
gives the same map. The corresponding left mates commute with tensor
associators, also on complexes and under rationalization. Hence each indicated
component is a commuting morphism of Weil pairs. Its inverse commutes as well;
faithfulness of forgetting the structure gives naturality and uniqueness. -/
theorem weilScalarAssociator_exists {E F G : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) (k : F ≤ G) :
    ∃! a : weilScalarExtension D c X₀ h ⋙ weilScalarExtension D c X₀ k ≅
        weilScalarExtension D c X₀ (h.trans k),
      ∀ K : WeilD D c X₀ E,
        (a.hom.app K).hom.f =
          (pbcScalarAssociator c.l c.Qbar (D.geometricFiber X₀).left
            (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
            (weilGeometricFiber_coefficientHypotheses D c X₀).2.2 h k).hom.app K.carrier := by
  exact CategoryTheory.Endofunctor.IsoAlgebra.normalized_associator_exists
    (pbcScalarSystem c.l c.Qbar (D.geometricFiber X₀).left
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.2)
    (fun E ↦ pbcRationalIsoPullback (D.geometricFrobenius X₀)
      (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E))
    (fun a ↦ pbcIsoRationalScalarComparison c.l c.Qbar (D.geometricFrobenius X₀)
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.2 a) h k
    (pbcIsoRationalScalarComparison_comp c.l c.Qbar (D.geometricFrobenius X₀)
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.2 h k)

/-- Tensor balancing induces the associator on the fixed-pair categories.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilScalarAssociator {E F G : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) (k : F ≤ G) :
    weilScalarExtension D c X₀ h ⋙ weilScalarExtension D c X₀ k ≅
        weilScalarExtension D c X₀ (h.trans k) :=
  (weilScalarAssociator_exists D c X₀ h k).exists.choose

attribute [local irreducible] weilScalarAssociator

set_option backward.isDefEq.respectTransparency false in
/-- The induced associators satisfy the same cocycle equality as tensor balancing.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: forget to the coefficient category and use the defining component
equations and the tensor associator pentagon. The forgetful functor is
faithful, giving the equality of commuting morphisms of pairs. -/
theorem weilScalarAssociator_cocycle
    {E F G H : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) (k : F ≤ G) (j : G ≤ H) (K : WeilD D c X₀ E) :
    (weilScalarExtension D c X₀ j).map ((weilScalarAssociator D c X₀ h k).hom.app K) ≫
        (weilScalarAssociator D c X₀ (h.trans k) j).hom.app K =
      (weilScalarAssociator D c X₀ k j).hom.app ((weilScalarExtension D c X₀ h).obj K) ≫
        (weilScalarAssociator D c X₀ h (k.trans j)).hom.app K := by
  exact CategoryTheory.Endofunctor.IsoAlgebra.normalized_cocycle
    (pbcScalarSystem c.l c.Qbar (D.geometricFiber X₀).left
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.2)
    (fun E ↦ weilFrobeniusPullback D c X₀ E)
    (fun a ↦ weilFrobeniusScalarComparison D c X₀ a)
    (fun a b ↦ weilScalarAssociator D c X₀ a b)
    (fun a b L ↦ by
      unfold weilScalarAssociator
      exact (weilScalarAssociator_exists D c X₀ a b).exists.choose_spec L) h k j K

/-- The concrete system of Weil categories with its induced tensor associators.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilScalarSystem :
    StageSystem (fun E : Padic.FiniteCoefficientFields c.l c.Qbar ↦ WeilD D c X₀ E) where
  T h := weilScalarExtension D c X₀ h
  assoc h k := weilScalarAssociator D c X₀ h k
  cocycle h k j K := weilScalarAssociator_cocycle D c X₀ h k j K

/-- The algebraic-closure coefficient category is the common-stage pair category
of the finite Weil stages. Objects are (E,W). Morphisms are representatives
(M,u), modulo equality at a common larger coefficient field, transported by the
specified tensor associators. Composition is at a common stage. In particular
this is the filtered colimit of the Weil categories themselves.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
abbrev WeilDQbar := (weilScalarSystem D c X₀).PairCategory

end WeilConjectures
