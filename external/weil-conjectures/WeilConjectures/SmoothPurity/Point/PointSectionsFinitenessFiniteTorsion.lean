/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleSheafOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Point
import Mathlib.RingTheory.Finiteness.Cardinality

/-! Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509
(blueprint: lem-weil-point-sections-finite-torsion). -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Constructible finite-ring point sections form a finite set.
Source: blueprint order 1509, finite-torsion clause
(blueprint: lem-weil-point-sections-finite-torsion).
Proof: etale origin, the comparison unit, and finite etale sections identify these
sections with a finitely generated module over the finite coefficient ring. -/
theorem point_finiteSections_finite_of_constructible (k B : Type u) [Field k] [IsAlgClosed k]
    [CommRing B] [Finite B]
    (F : proEtaleRingModules (Spec (.of k)) (proEtaleConstantRing (Spec (.of k)) B))
    (hF : IsConstructibleProEtaleModuleSheaf (Spec (.of k)) B F) :
    Finite ((pointFiniteSections k B).obj F) := by
  classical
  let T := Spec (.of k)
  let A := ULift.{u + 1, u} B
  obtain ⟨e, α, _⟩ := finiteRing_constructibleSheaf_origin T B
  let F' : ObjectProperty.FullSubcategory (IsConstructibleProEtaleModuleSheaf T B) := ⟨F, hF⟩
  let G := e.inverse.obj F'
  have hG : IsConstructibleSheaf G.obj :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G.obj).mp G.property
  letI := hG
  letI : Module.Finite A ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj G.obj) :=
    Etale.finite_Γ_of_isConstructibleSheaf G.obj
  have hfin : Finite ((Sheaf.Γ T.smallEtaleTopology
      (ModuleCat.{u + 1} A)).obj G.obj) := Module.finite_of_finite A
  let ev := (sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (op (Etale.mk (𝟙 T)))
  let eΓ := (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (isTerminalEtalePoint)).app G.obj
  letI := hfin
  have hGsec : Finite (ev.obj G.obj) :=
    Finite.of_equiv _ eΓ.toLinearEquiv.toEquiv
  letI := hGsec
  let η := (T.proEtaleSiteComparisonModules A).unit.app G.obj
  letI : IsIso η := (siteComparison_finiteLevel T A).2.2.1 G.obj
  let eη := ev.mapIso (asIso η)
  have hLsec : Finite (((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj G.obj).obj.obj
      (op (ProEt.mk (𝟙 T)))) :=
    @Finite.of_equiv _ _ hGsec eη.toLinearEquiv.toEquiv
  letI := hLsec
  let ea := ((sheafSections (ProEt.topology T) AddCommGrpCat.{u + 1}).obj
    (op (ProEt.mk (𝟙 T)))).mapIso (α.app G)
  have heF : Finite ((e.functor.obj G).obj.val.obj (op (ProEt.mk (𝟙 T)))) :=
    @Finite.of_surjective _ _ hLsec ea.hom
      (ConcreteCategory.bijective_of_isIso ea.hom).2
  letI := heF
  let ec := (pointFiniteSections k B).mapIso
    ((ObjectProperty.ι (IsConstructibleProEtaleModuleSheaf T B)).mapIso (e.counitIso.app F'))
  exact @Finite.of_equiv _ _ heF ec.toLinearEquiv.toEquiv

/-- Strictly separated finite torsion clause from the point-sections finiteness assertion.
Proof: finite-ring constructible sheaves have etale origin. The comparison unit
identifies their pro-etale sections with etale sections. Constructible etale sections
over an algebraically closed point are finitely generated, hence finite over the finite
coefficient ring. Exact evaluation and restriction of scalars commute with cohomology
and preserve zero objects, giving the same finite cohomological support.
Source: the landing assertion in the finite coefficient point construction;
(blueprint: lem-weil-point-sections-finite-torsion).
-/
theorem point_sections_finiteness_finiteTorsion (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ C : CochainComplex
        (SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology (Spec (.of D.k)))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}).obj
                (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))))) ℤ,
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) (DerivedCategory.Q.obj C) →
        DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
          (DerivedCategory.Q.obj
            (((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex
              (.up ℤ)).obj C))) := by
  classical
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  intro C hC
  let B := Padic.coefficientExtensionRing l E n
  letI : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  let A := (constantSheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} B))
  letI : PreservesFiniteLimits (pointModuleSections D.k A) :=
    ((@point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A).1
  letI : PreservesFiniteColimits (pointModuleSections D.k A) :=
    ((@point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A).2.1
  let F := pointFiniteSections D.k B
  letI : PreservesFiniteLimits F := inferInstanceAs (PreservesFiniteLimits
    (pointModuleSections D.k A ⋙ ModuleCat.restrictScalars (pointConstantSectionMap D.k B)))
  letI : PreservesFiniteColimits F := inferInstanceAs (PreservesFiniteColimits
    (pointModuleSections D.k A ⋙ ModuleCat.restrictScalars (pointConstantSectionMap D.k B)))
  let iso (i : ℤ) :
      (DerivedCategory.homologyFunctor _ i).obj
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C)) ≅
        F.obj ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj C)) :=
    (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
      (C.sc i).mapHomologyIso F ≪≫
        F.mapIso ((DerivedCategory.homologyFunctorFactors _ i).app C).symm
  constructor
  · refine ⟨hC.1.toFinset, fun i hi ↦ ?_⟩
    have hzero : IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (DerivedCategory.Q.obj C)) := by
      by_contra h
      exact hi (hC.1.mem_toFinset.mpr h)
    exact IsZero.of_iso (F.map_isZero hzero) (iso i)
  · intro i
    haveI := point_finiteSections_finite_of_constructible D.k B _ (hC.2 i)
    exact Finite.of_equiv _ (iso i).toLinearEquiv.symm.toEquiv

end WeilConjectures
