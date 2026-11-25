/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraFrobenius
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedGlobalSectionsTransport
public import WeilConjectures.WeilSheaf.CohomologyExact

/-!
# The equivalence on constant-sheaf cohomology induced by a geometric isomorphism

The cohomology `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf is, after forgetting its Frobenius,
the cohomology of the derived global sections `RΓ(X̄, ℚ̄_ℓ)` of the constant `ℓ`-adic sheaf on the
geometric fiber (`AlgebraicGeometry.WeilSheaf.cohomologyCarrierIso`): forgetting the Weil
structure commutes with right derivation, and global sections over `Spec k̄` are exact. Under this
identification the Frobenius is the transport of `RΓ(X̄, ℚ̄_ℓ)` along the inverse of the geometric
Frobenius of `X̄` (`AlgebraicGeometry.WeilSheaf.cohomologyCarrierIso_hom_frobenius`).

An isomorphism `e : Ȳ ≅ X̄` of geometric fibers, over possibly different finite fields, therefore
induces a linear equivalence `Hⁱ(Y ⊗ k̄', ℚ̄_ℓ) ≃ Hⁱ(X ⊗ k̄, ℚ̄_ℓ)`
(`AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso`), the transport of
`RΓ(-, ℚ̄_ℓ)` along `e`. This is the isomorphism-invariance part of the base-change clause of
`theorem-poincare-duality-frobenius`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

section

variable (k : Type u) [Field k] [Finite k] (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  [X.Over (Spec (.of k))]

instance : (IsoAlgebra.forget (frobeniusPullback k l X)).PreservesKInjectiveComplexes := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (.of k)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (.of k)).geometricFiber) ℤ
  infer_instance

instance : PreservesFiniteLimits
    (ProEtale.adicGlobalSections l (Spec (.of k) ↘ Spec (.of k)).geometricFiber) := by
  unfold ProEtale.adicGlobalSections
  infer_instance

instance : PreservesFiniteColimits
    (ProEtale.adicGlobalSections l (Spec (.of k) ↘ Spec (.of k)).geometricFiber) := by
  have : (ProEtale.adicGlobalSections l
      (Spec (.of k) ↘ Spec (.of k)).geometricFiber).PreservesEpimorphisms := by
    unfold ProEtale.adicGlobalSections
    infer_instance
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (ProEtale.adicGlobalSections l (Spec (.of k) ↘ Spec (.of k)).geometricFiber)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end

variable (k : Type u) [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- The derived pushforward `Ra_* ℚ̄_ℓ` of the constant Weil sheaf along the structure morphism,
in the derived category of pro-étale Weil sheaves on `Spec k₀`. -/
noncomputable abbrev derivedLowerStarAdicConstant :
    DerivedCategory (ProEtaleWeilSheaf k l (Spec (.of k))) :=
  (ProEtaleWeilSheaf.lowerStar k l (X ↘ Spec (.of k))).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor _ 0).obj (ProEtaleWeilSheaf.adicConstant k l X))

/-- **The carrier of constant-sheaf cohomology.** Forgetting its Frobenius, the cohomology
`Hⁱ(X ⊗ k̄, ℚ̄_ℓ) = Γ(Spec k̄, 𝓗ⁱ(Ra_* ℚ̄_ℓ))` is `Hⁱ RΓ(X̄, ℚ̄_ℓ)`: global sections over `Spec k̄`
are exact, and `Γ(Spec k̄, -) ∘ Ra_* ≅ RΓ(X̄, -)` after forgetting the Weil structures. -/
noncomputable def cohomologyCarrierIso (i : ℤ) :
    (IsoAlgebra.forget _ ⋙
        ProEtale.adicGlobalSections l (Spec (.of k) ↘ Spec (.of k)).geometricFiber).obj
        ((DerivedCategory.homologyFunctor _ i).obj (derivedLowerStarAdicConstant k l X)) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        (ProEtale.derivedGlobalSectionsUnit l (X ↘ Spec (.of k)).geometricFiber) :=
  ((IsoAlgebra.forget _ ⋙ ProEtale.adicGlobalSections l
      (Spec (.of k) ↘ Spec (.of k)).geometricFiber).mapDerivedCategoryHomologyFunctorIso i).app _ ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      ((IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetCompIso
          (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l (X ↘ Spec (.of k))
            (comp_over (X ↘ Spec (.of k)) (Spec (.of k))))
          (ProEtale.adicLowerStarCompGlobalSectionsIso l
            (Scheme.Hom.geometricFiberMap (X ↘ Spec (.of k))
              (comp_over (X ↘ Spec (.of k)) (Spec (.of k)))))).app _ ≪≫
        (ProEtale.adicGlobalSections l (X ↘ Spec (.of k)).geometricFiber).rightDerivedFunctor.mapIso
          (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app _))

/-- The Frobenius of `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` is the automorphism of global sections over `Spec k̄`
induced by the Weil structure of the cohomology sheaf `𝓗ⁱ(Ra_* ℚ̄_ℓ)`. -/
lemma cohomology_adicConstant_frobenius (i : ℤ) :
    ((adicConstant k l X).cohomology i).frobenius = WeilCoefficients.linearEquivOfIso
      ((IsoAlgebra.forgetCompIsoOfIso (ProEtale.adicLowerStarCompGlobalSectionsIso l
        (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)).app
          ((DerivedCategory.homologyFunctor _ i).obj (derivedLowerStarAdicConstant k l X))) :=
  rfl

omit [Fact (ringChar k ≠ l)] [QuasiCompact (X ↘ Spec (.of k))]
  [QuasiSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- **The Frobenius of constant-sheaf cohomology is the transport along the geometric Frobenius.**
Under `Hⁱ(X ⊗ k̄, ℚ̄_ℓ) ≅ Hⁱ RΓ(X̄, ℚ̄_ℓ)`, the Frobenius is induced by the transport of
`RΓ(X̄, ℚ̄_ℓ)` along the inverse of the geometric Frobenius of `X̄`. -/
lemma cohomologyCarrierIso_hom_frobenius (i : ℤ) :
    (IsoAlgebra.forgetCompIsoOfIso (ProEtale.adicLowerStarCompGlobalSectionsIso l
        (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)).hom.app
          ((DerivedCategory.homologyFunctor _ i).obj (derivedLowerStarAdicConstant k l X)) ≫
        (cohomologyCarrierIso k l X i).hom =
      (cohomologyCarrierIso k l X i).hom ≫ (DerivedCategory.homologyFunctor _ i).map
        (ProEtale.derivedGlobalSectionsUnitIso l
          (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.symm).hom := by
  have hG := Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality
    (IsoAlgebra.forgetCompIsoOfIso (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)) i
    (derivedLowerStarAdicConstant k l X)
  have hB := IsoAlgebra.mapDerivedCategoryNatIso_forgetCompIsoOfIso_hom_app_rightDerivedFunctor_obj
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l (X ↘ Spec (.of k))
      (comp_over (X ↘ Spec (.of k)) (Spec (.of k))))
    (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (Scheme.Hom.geometricFiberMap (X ↘ Spec (.of k))
        (comp_over (X ↘ Spec (.of k)) (Spec (.of k)))))
    (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)
    (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)
    (fun M ↦ ProEtale.adicLowerStarCompGlobalSectionsIso_inv_app_comm l _ _ _ _ _ M)
    ((DerivedCategory.singleFunctor _ 0).obj (ProEtaleWeilSheaf.adicConstant k l X))
  simp only [cohomologyCarrierIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [reassoc_of% hG]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  simp only [← Functor.map_comp]
  refine congrArg (DerivedCategory.homologyFunctor _ i).map ?_
  erw [reassoc_of% hB]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  have h₁ := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor
    (IsoAlgebra.forget (frobeniusPullback k l X)) (frobeniusPullback k l X)
    (ProEtaleWeilSheaf.adicConstant k l X)
  have h₂ := Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor
    (IsoAlgebra.strNatIso (frobeniusPullback k l X)) (ProEtaleWeilSheaf.adicConstant k l X)
  simp only [ProEtale.derivedGlobalSectionsUnitIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  have hn := (Functor.rightDerivedFunctorIsoMapDerivedCategoryComp
    (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)).hom.naturality
    (((IsoAlgebra.forget (frobeniusPullback k l X)).mapDerivedCategorySingleFunctor 0).hom.app
      (ProEtaleWeilSheaf.adicConstant k l X))
  erw [reassoc_of% hn]
  refine congrArg (_ ≫ ·) ?_
  simp only [← Functor.map_comp]
  refine congrArg _ ?_
  rw [Category.assoc, h₂, ← h₁]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rfl

/-- The linear equivalence induced by an isomorphism of geometric fibers: the transport of
`RΓ(Ȳ, ℚ̄_ℓ) ≅ RΓ(X̄, ℚ̄_ℓ)` along `e`, through the identifications
`AlgebraicGeometry.WeilSheaf.cohomologyCarrierIso` of the carriers of the cohomology of the
constant Weil sheaves. This is an ingredient of the base-change clause of
`theorem-poincare-duality-frobenius`. -/
noncomputable def cohomologyLinearEquivOfGeometricFiberIso
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber) (i : ℤ) :
    ((WeilSheaf.adicConstant k' l Y).cohomology i).carrier ≃ₗ[PadicAlgCl l]
      ((WeilSheaf.adicConstant k l X).cohomology i).carrier :=
  WeilCoefficients.linearEquivOfIso
    (cohomologyCarrierIso k' l Y i ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (ProEtale.derivedGlobalSectionsUnitIso l e) ≪≫
        (cohomologyCarrierIso k l X i).symm)

end AlgebraicGeometry.WeilSheaf
