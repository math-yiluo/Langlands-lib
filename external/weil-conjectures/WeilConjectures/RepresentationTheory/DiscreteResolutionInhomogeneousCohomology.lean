/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.RepresentationTheory.DiscreteIntegerInvariantsInfrastructure
public import WeilConjectures.RepresentationTheory.LocallyConstantCochainsEffaceable
public import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
public import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Injective resolutions and locally constant inhomogeneous cochains

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
section-continuous-group-cohomology, profinite comparison.
(blueprint: lem-sc-discrete-resolution-inhomogeneous-cohomology).
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

/-- The isomorphism in degree `q` between two universal cohomological delta-functors induced by
an isomorphism of their degree-zero parts. -/
noncomputable def _root_.CategoryTheory.CohomologicalDeltaFunctor.isoOfIsUniversal
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (T R : CohomologicalDeltaFunctor C D) (hT : T.IsUniversal) (hR : R.IsUniversal)
    (e : T.F 0 ≅ R.F 0) (q : ℕ) : T.F q ≅ R.F q := by
  let α := (hT R e.hom).exists.choose
  let β := (hR T e.inv).exists.choose
  have hα : α.app 0 = e.hom := (hT R e.hom).exists.choose_spec
  have hβ : β.app 0 = e.inv := (hR T e.inv).exists.choose_spec
  let idT : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ 𝟙 (T.F n), by intros; simp⟩
  let idR : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ 𝟙 (R.F n), by intros; simp⟩
  let αβ : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ α.app n ≫ β.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [α.naturality S hS n]
      simp only [Category.assoc]
      rw [β.naturality S hS n]⟩
  let βα : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ β.app n ≫ α.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [β.naturality S hS n]
      simp only [Category.assoc]
      rw [α.naturality S hS n]⟩
  have hαβ : αβ = idT := (hT T (𝟙 (T.F 0))).unique
    (by change α.app 0 ≫ β.app 0 = _; rw [hα, hβ]; exact e.hom_inv_id)
    rfl
  have hβα : βα = idR := (hR R (𝟙 (R.F 0))).unique
    (by change β.app 0 ≫ α.app 0 = _; rw [hβ, hα]; exact e.inv_hom_id)
    rfl
  refine ⟨α.app q, β.app q, ?_, ?_⟩
  · exact congrArg (fun f : CohomologicalDeltaFunctor.Hom T T ↦ f.app q) hαβ
  · exact congrArg (fun f : CohomologicalDeltaFunctor.Hom R R ↦ f.app q) hβα

@[simp]
theorem _root_.CategoryTheory.CohomologicalDeltaFunctor.isoOfIsUniversal_hom_zero
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (T R : CohomologicalDeltaFunctor C D) (hT : T.IsUniversal) (hR : R.IsUniversal)
    (e : T.F 0 ≅ R.F 0) : (T.isoOfIsUniversal R hT hR e 0).hom = e.hom :=
  (hT R e.hom).exists.choose_spec

/-- Additive equivalence between the homology of the invariants of an injective resolution
transported through an abelian equivalence and the homology of any complex with the locally
constant inhomogeneous terms and differential.

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
section-continuous-group-cohomology, final profinite comparison.
(blueprint: lem-sc-discrete-resolution-inhomogeneous-cohomology).

Proof: On discrete integer representations construct the functorial complex whose degree
n is the abelian group of locally constant maps G^n to the coefficient module, with the
inhomogeneous differential displayed below. The differential squares to zero by cancellation
of the face maps. Surjections of coefficients induce surjections on terms: a locally
constant map on the compact space G^n has finite image, and choosing lifts of its finitely
many values preserves local constancy. Kernels are computed pointwise, so short exact
sequences give short exact sequences of complexes. The homology long exact sequence is
natural and gives a cohomological delta-functor. Its degree zero is invariants since the
first differential is g acting on m minus m.
Embed M into locally constant maps G to M by m mapping to the orbit function x acting on m,
with right translation action on the functions. Every such function has an open stabilizer:
its finite clopen partition has a common stabilizing open subgroup, by compactness and
continuity of multiplication. For this coinduced module the insertion operator on
inhomogeneous cochains, h(F)(g1,...,g(n-1))(x) = F(x,g1,...,g(n-1))(1), is locally
constant and satisfies dh+hd=1 in positive degrees, by expansion of the differential.
Thus the delta-functor is effaceable. Equivalences preserve injectives and exactness, so
transporting resolutions across E gives derived invariants on the original category.
The discrete representation category is abelian: kernels and cokernels are the underlying
module kernels and cokernels, and open stabilizers pass to subobjects and quotients.
It has enough injectives even over the integers. Embed the underlying abelian group of M
into an injective abelian group J; locally constant maps G to J with right translation
are right adjoint to the exact forgetful functor and hence injective. The map sending m
to (g mapping to the image of g acting on m in J) is an equivariant monomorphism.
Transport these injectives and resolutions along E.
Universality of the two effaceable delta-functors and their degree-zero identification
give inverse comparisons in all degrees. No global choice of a resolution in the original
category is needed: compare the given resolution with one transported from the discrete
category, using the comparison theorem and its homotopy uniqueness. Finally t identifies
K termwise with the constructed complex. The differential equation gives a complex
isomorphism; transport homology along it. This proof uses arbitrary integer modules,
not a finite scalar ring. In degree zero there are no incoming boundaries. -/
noncomputable def invariantResolutionHomologyAddEquivInhomogeneous
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).Additive]
    (F : A) (I : InjectiveResolution F)
    (K : CochainComplex AddCommGrpCat.{max u s} ℕ)
    (t : ∀ n : ℕ, K.X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj F).obj.V)
    (ht : ∀ (n : ℕ) (x : K.X n) (g : Fin (n + 1) → G),
      t (n + 1) ((K.d n (n + 1)) x) g =
        (E.functor.obj F).obj.ρ (g 0) (t n x (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • t n x (Fin.contractNth k (· * ·) g))
    (q : ℕ) :
    ((((E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology q) ≃+ K.homology q := by
  classical
  let V := E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
    forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat
  have hinfra := discreteInteger_invariants_infrastructure G A E
  letI : EnoughInjectives A := hinfra.1
  letI : CategoryTheory.Limits.PreservesFiniteLimits V := hinfra.2
  have hC := exists_locallyConstantCochains_effaceable G A E
  have hC₁ := hC.choose_spec
  set C := hC.choose
  clear_value C
  have hC₂ := hC₁.choose_spec
  set e := hC₁.choose
  clear_value e
  obtain ⟨-, hd, hT'⟩ := hC₂
  have hT₁ := hT'.choose_spec
  set T := hT'.choose
  clear_value T
  obtain ⟨hTF, hTzero, heff⟩ := hT₁
  let hTzero := Classical.choice hTzero
  have hT : T.IsUniversal := effaceable_deltaFunctor_isUniversal T heff
  have hR' := V.exists_universal_rightDerived_deltaFunctor
  have hR₁ := hR'.choose_spec
  set R := hR'.choose
  clear_value R
  obtain ⟨hRF, hR, hRzero⟩ := hR₁
  let hRzero' : R.F 0 ≅ V := eqToIso (congrFun hRF 0) ≪≫ Classical.choice hRzero
  let comparison : V.rightDerived q ≅ C ⋙ HomologicalComplex.homologyFunctor
      AddCommGrpCat.{max u s} (ComplexShape.up ℕ) q :=
    eqToIso (congrFun hRF q).symm ≪≫
      CohomologicalDeltaFunctor.isoOfIsUniversal R T hR hT (hRzero' ≪≫ hTzero.symm) q ≪≫
        eqToIso (congrFun hTF q)
  let coord : ∀ n : ℕ, (C.obj F).X n ≅ K.X n :=
    fun n ↦ ((e F n).trans (t n).symm).toAddCommGrpIso
  have hcoord : ∀ (n : ℕ) (x : (C.obj F).X n),
      (coord n).hom x = (t n).symm (e F n x) := by
    intros
    rfl
  let iso : C.obj F ≅ K := HomologicalComplex.Hom.isoOfComponents coord (by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    ext x
    apply (t (i + 1)).injective
    apply LocallyConstant.ext
    intro g
    change t (i + 1) (K.d i (i + 1) ((coord i).hom x)) g =
      t (i + 1) ((coord (i + 1)).hom ((C.obj F).d i (i + 1) x)) g
    rw [ht, hcoord, hcoord]
    simp only [AddEquiv.apply_symm_apply]
    exact (hd F i x g).symm)
  let h : (((V.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q)
      ≅ K.homology q :=
    (I.isoRightDerivedObj V q).symm ≪≫ comparison.app F ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) q).mapIso iso
  exact h.addCommGroupIsoToAddEquiv

end Rep
