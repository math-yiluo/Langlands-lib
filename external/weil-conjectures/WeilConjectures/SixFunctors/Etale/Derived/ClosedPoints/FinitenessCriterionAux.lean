/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.ConstructibleApproximation
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FiniteSections
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Hypercohomology
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Acyclic
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Detection
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber
public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtensionIso

/-!
# Auxiliary lemmas for Deligne's finiteness criterion at closed points

Finiteness of the cohomology of bounded constructible complexes on separably closed points and on
proper schemes over a separably closed field, stalks of pullbacks at the points of a source, and
the bounded constructibility of truncations, used in
`WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterion`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory.TStructure (t)

section Auxiliary

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- In an exact sequence of modules over a finite ring, the middle term is finite as soon as the
outer terms are. -/
lemma finite_X₂_of_exact {S : ShortComplex (ModuleCat.{u + 1} Λ)} (hS : S.Exact)
    (h₁ : Finite S.X₁) (h₃ : Finite S.X₃) : Finite S.X₂ := by
  have := isNoetherian_of_range_eq_ker S.f.hom S.g.hom hS.moduleCat_range_eq_ker
  exact Module.finite_of_finite Λ

variable {k : Type u} [Field k] [IsSepClosed k]

omit [Finite Λ] in
/-- Over a separably closed field `k`, the derived global sections `RΓ(Spec k, M)` of a bounded
constructible complex `M` are bounded with finite cohomology. -/
lemma boundedFiniteCohomology_rightDerivedGlobalSections_of_isSepClosed
    {M : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) M) :
    _root_.DerivedCategory.boundedFiniteCohomology Λ
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj M) :=
  (_root_.DerivedCategory.boundedFiniteCohomology Λ).prop_of_iso
    ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app M).symm
    ((boundedConstructible_iff_boundedFiniteCohomology M).1 hM)

omit [Finite Λ] in
/-- If the derived direct image `Rp_* K` to a separably closed point is bounded constructible,
then the derived global sections `RΓ(X, K) = RΓ(Spec k, Rp_* K)` are bounded with finite
cohomology. -/
lemma boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj K)) :
    _root_.DerivedCategory.boundedFiniteCohomology Λ
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K) :=
  (_root_.DerivedCategory.boundedFiniteCohomology Λ).prop_of_iso
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) p).app K)
    (boundedFiniteCohomology_rightDerivedGlobalSections_of_isSepClosed hK)

/-- For `X` proper over a separably closed field, the derived global sections `RΓ(X, K)` of a
bounded constructible complex `K` are bounded with finite cohomology. -/
lemma boundedFiniteCohomology_rightDerivedGlobalSections_of_isProper
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    _root_.DerivedCategory.boundedFiniteCohomology Λ
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K) :=
  boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar p
    (boundedConstructible_rightDerivedLowerStar_of_isProper (𝟙 _) p hK)

omit [Finite Λ] in
/-- The stalk of a sheaf `F` at the geometric point over `h w` vanishes as soon as the stalk of
the pullback `h^* F` at the geometric point over `w` does: the geometric point of `W` over `w`,
followed by `h`, factors through the geometric point of `X` over `h w`. -/
lemma isZero_sheafFiber_algClosurePoint_apply_of_isZero_sheafFiber_upperStar {X W : Scheme.{u}}
    (h : W ⟶ X) (w : W) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsZero ((pointSmallEtale (W.algClosurePoint w)).sheafFiber.obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).obj F))) :
    IsZero ((pointSmallEtale (X.algClosurePoint (h w))).sheafFiber.obj F) := by
  let φ := h.residueFieldMap w
  let : Algebra (X.residueField (h w)) (AlgebraicClosure (W.residueField w)) :=
    (φ ≫ CommRingCat.ofHom (algebraMap (W.residueField w) _)).hom.toAlgebra
  let j : AlgebraicClosure (X.residueField (h w)) →ₐ[X.residueField (h w)]
      AlgebraicClosure (W.residueField w) := IsAlgClosed.lift
  let a : Spec (.of (AlgebraicClosure (W.residueField w))) ⟶
      Spec (.of (AlgebraicClosure (X.residueField (h w)))) :=
    Spec.map (CommRingCat.ofHom j.toRingHom)
  have ha : a ≫ X.algClosurePoint (h w) = W.algClosurePoint w ≫ h := by
    change a ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (h w)) _)) ≫
        X.fromSpecResidueField (h w) =
      (Spec.map (CommRingCat.ofHom (algebraMap (W.residueField w) _)) ≫
        W.fromSpecResidueField w) ≫ h
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext x
    exact j.commutes x
  refine IsZero.of_iso ?_ ((Scheme.sheafFiberPrecompIso _ a (ModuleCat.{u + 1} Λ)).app F)
  rw [ha]
  exact hF.of_iso ((Etale.upperStarCompSheafFiberIso _ h _).app F).symm

omit [Finite Λ] in
/-- If `G ∈ D^{≥ m}` has constructible cohomology sheaves in degrees `< q`, then its truncation
`τ^{< q} G` is bounded constructible. -/
lemma boundedConstructible_truncLT_of_isGE {X : Scheme.{u}}
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m q : ℤ)
    [G.IsGE m]
    (hG : ∀ j < q, IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ j).obj G)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ((t.truncLT q).obj G) := by
  have e (j : ℤ) (hj : j < q) :=
    have := _root_.DerivedCategory.isIso_homologyFunctor_map_truncLTι_app G q j hj
    asIso ((_root_.DerivedCategory.homologyFunctor _ j).map ((t.truncLTι q).app G))
  have hz (j : ℤ) (hj : q ≤ j) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj ((t.truncLT q).obj G)) :=
    _root_.DerivedCategory.isZero_of_isLE _ (q - 1) j (by lia)
  refine ⟨⟨⟨m, ?_⟩, ⟨q - 1, inferInstance⟩⟩, fun j ↦ ?_⟩
  · refine (_root_.DerivedCategory.isGE_iff _ m).2 fun j hj ↦ ?_
    rcases lt_or_ge j q with hjq | hjq
    · exact (_root_.DerivedCategory.isZero_of_isGE G m j hj).of_iso (e j hjq)
    · exact hz j hjq
  · rcases lt_or_ge j q with hjq | hjq
    · have := hG j hjq
      exact IsConstructibleSheaf.of_iso
        (F := (_root_.DerivedCategory.homologyFunctor _ j).obj G) (e j hjq).symm
    · exact IsConstructibleSheaf.of_isZero (hz j hjq)

end Auxiliary

end Etale

end AlgebraicGeometry
