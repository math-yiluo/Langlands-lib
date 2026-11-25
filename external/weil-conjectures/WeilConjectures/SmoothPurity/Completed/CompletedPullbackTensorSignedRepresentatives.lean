/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
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

/-! # Signed exchange for coherent pullback tensor representatives

Source: Stacks 07A4 and the Koszul sign rules, Tag 0FNG.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local implicit_reducible] pullbackTensorSwap 
  pullbackTensorSequenceDerived coefficientTotalTensor Functor.map₂HomologicalComplex
  pullbackTensorSequenceDirect
attribute [local irreducible] HasDerivedCategory.standard
  pullbackTensorCalculus pullbackTensorSequenceInverse
  Functor.leftAdjoint pullbackTensorSequenceAdjunction
  pullbackTensorSequenceCochain pullbackTensorSystemComparison pullbackTensorBraiding
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  pullbackTensorSignedTotal pullbackTensorSequenceRing
  SheafOfModules.monoidalCategory PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification HomologicalComplex₂.total
  CategoryTheory.Functor.mapBifunctorHomologicalComplex

private theorem signedSectionSquare
    {A B C D E F : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    (σ : A →+ B) (η : B →+ D) (κ' : D →+ F)
    (η' : A →+ C) (κ : C →+ E) (τ : E →+ F)
    (x : A) (x' : B) (y : E) (y' : F) (ε : ℤˣ)
    (hσ : σ x = ε • x') (hκ' : κ' (η x') = y')
    (hκ : κ (η' x) = y) (hτ : τ y = ε • y') :
    κ' (η (σ x)) = τ (κ (η' x)) := by
  rw [hσ]
  simp only [Units.smul_def, map_zsmul]
  rw [hκ', hκ, hτ]
  rfl

private theorem normalizedSignedSquare
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : D × D ⥤ D)
    (β : T ≅ pullbackTensorSwap D ⋙ T)
    {M N U V : C} {A B M' N' U' V' : D}
    (b : U ⟶ V) (c : U' ⟶ V')
    (r : U ≅ M) (s : V ≅ N)
    (r' : U' ≅ T.obj (M', N')) (s' : V' ≅ T.obj (N', M'))
    (e : F.obj U ≅ U') (e' : F.obj V ≅ V')
    (j : M ⟶ N) (a : F.obj M ⟶ T.obj (A, B))
    (a' : F.obj N ⟶ T.obj (B, A))
    (x : A ≅ M') (y : B ≅ N')
    (h : b ≫ s.hom = r.hom ≫ j)
    (h' : c ≫ s'.hom = r'.hom ≫ β.hom.app (M', N'))
    (hn : F.map b ≫ e'.hom = e.hom ≫ c)
    (hr : F.map r.hom ≫ a ≫ T.map (Prod.mkHom x.hom y.hom) = e.hom ≫ r'.hom)
    (hs : F.map s.hom ≫ a' ≫ T.map (Prod.mkHom y.hom x.hom) = e'.hom ≫ s'.hom) :
    F.map j ≫ a' = a ≫ β.hom.app (A, B) := by
  apply (cancel_epi (F.mapIso r).hom).1
  apply (cancel_mono (T.mapIso (Iso.prod y x)).hom).1
  simp only [Functor.mapIso_hom, Iso.prod_hom, Category.assoc]
  calc
    _ = F.map b ≫ (F.map s.hom ≫ a' ≫ T.map (Prod.mkHom y.hom x.hom)) := by
      rw [← F.map_comp_assoc, ← h, F.map_comp_assoc]
    _ = e.hom ≫ c ≫ s'.hom := by rw [hs, ← Category.assoc, hn, Category.assoc]
    _ = (F.map r.hom ≫ a ≫ T.map (Prod.mkHom x.hom y.hom)) ≫
        β.hom.app (M', N') := by rw [h', hr]; simp only [Category.assoc]
    _ = _ := by
      have hβ := β.hom.naturality (Prod.mkHom x.hom y.hom)
      dsimp only [Functor.comp_map, pullbackTensorSwap] at hβ
      simp only [Category.assoc]
      rw [hβ]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- The section calculation elaborates the tensor sheafification and adjunction models.
private theorem coherentSignedTotal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    let L := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    L.map (pullbackTensorSignedTotal
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P Q).hom ≫
        (pullbackTensorSequenceCochain l E f).hom.app (Q,P) =
      (pullbackTensorSequenceCochain l E f).hom.app (P,Q) ≫
        (pullbackTensorSignedTotal
          (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X) (L.obj P) (L.obj Q)).hom := by
  let L := pullbackTensorSequenceInverse l E f
  let adj := pullbackTensorSequenceAdjunction l E f
  let κ := pullbackTensorSequenceCochain l E f
  let σY := pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y) P Q
  let σX := pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)
    ((L.mapHomologicalComplex (.up ℤ)).obj P) ((L.mapHomologicalComplex (.up ℤ)).obj Q)
  have hκ := (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose_spec
  have hσY := (pullbackTensorSignedTotal_existsUnique
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y) P Q).exists.choose_spec
  have hσX := (pullbackTensorSignedTotal_existsUnique
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)
    ((L.mapHomologicalComplex (.up ℤ)).obj P)
    ((L.mapHomologicalComplex (.up ℤ)).obj Q)).exists.choose_spec
  apply HomologicalComplex.hom_ext
  intro k
  change L.map (σY.hom.f k) ≫ (κ.hom.app (Q,P)).f k =
    (κ.hom.app (P,Q)).f k ≫ σX.hom.f k
  apply (adj.homEquiv _ _).injective
  change adj.unit.app _ ≫ (pullbackTensorSequenceDirect l E f).map
      (L.map (σY.hom.f k) ≫ (κ.hom.app (Q,P)).f k) =
    adj.unit.app _ ≫ (pullbackTensorSequenceDirect l E f).map ((κ.hom.app (P,Q)).f k ≫ σX.hom.f k)
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality (σY.hom.f k)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (P.X p) (Q.X q)).inv).1
  apply (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change ((κ.hom.app (Q,P)).f k).val.app
      (op ((pullbackTensorSequenceBase f).obj U.unop))
      ((adj.unit.app _).val.app U
        ((σY.hom.f k).val.app U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y) P Q p q k hpq U x y))) =
    (σX.hom.f k).val.app (op ((pullbackTensorSequenceBase f).obj U.unop))
      (((κ.hom.app (P,Q)).f k).val.app
        (op ((pullbackTensorSequenceBase f).obj U.unop))
        ((adj.unit.app _).val.app U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y) P Q p q k hpq U x y)))
  let P' := (L.mapHomologicalComplex (.up ℤ)).obj P
  let Q' := (L.mapHomologicalComplex (.up ℤ)).obj Q
  let U' := op ((pullbackTensorSequenceBase f).obj U.unop)
  let xp := ((adj.unit.app (P.X p)).val.app U) x
  let yq := ((adj.unit.app (Q.X q)).val.app U) y
  let gY := coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y) Q P q p k ((add_comm q p).trans hpq) U y x
  let gX := coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X) P' Q' p q k hpq U' xp yq
  let gX' := coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X) Q' P' q p k
    ((add_comm q p).trans hpq) U' yq xp
  refine signedSectionSquare
    ((σY.hom.f k).val.app U).hom.toAddMonoidHom
    ((adj.unit.app (((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)).obj (Q,P)).X k)).val.app U).hom.toAddMonoidHom
    (((κ.hom.app (Q,P)).f k).val.app
      (op ((pullbackTensorSequenceBase f).obj U.unop))).hom.toAddMonoidHom
    ((adj.unit.app (((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q)).X k)).val.app U).hom.toAddMonoidHom
    (((κ.hom.app (P,Q)).f k).val.app
      (op ((pullbackTensorSequenceBase f).obj U.unop))).hom.toAddMonoidHom
    ((σX.hom.f k).val.app
      (op ((pullbackTensorSequenceBase f).obj U.unop))).hom.toAddMonoidHom
    _ gY gX gX' (p*q).negOnePow ?_ ?_ ?_ ?_
  · dsimp only [σY]
    unfold pullbackTensorSignedTotal
    exact hσY p q k hpq U x y
  · dsimp only [κ, adj]
    unfold pullbackTensorSequenceCochain pullbackTensorUniqueChoice
    exact hκ Q P q p k ((add_comm q p).trans hpq) U.unop y x
  · dsimp only [κ, adj]
    unfold pullbackTensorSequenceCochain pullbackTensorUniqueChoice
    exact hκ P Q p q k hpq U.unop x y
  · dsimp only [σX]
    unfold pullbackTensorSignedTotal
    exact hσX p q k hpq _ _ _

-- The normalization square retains both unbounded K-flat tensor models.
/-- Signed exchange for the coherent comparison on K-flat representatives.
Source: Stacks 07A4, the total tensor construction, and the symmetry sign rule
of Tag 0FNG (blueprint: lem-pur-completed-pullback-tensor-signed-representatives).
Proof: in bidegree (p,q), both chain maps send the adjunction-unit section of
x tensor y to (-1)^(p*q) times the tensor of the unit sections of y and x.
Naturality of the unit, linearity, tensor sheafification and total summand
injections prove equality of these chain maps. Apply the derived quotient.
The normalization of the coherent comparison and the normalization of both
signed braidings identify its four sides with the displayed derived square.
Cancel the invertible tensor-model comparisons and pullback factorizations.
This is the calculation on K-flat complexes; extension to arbitrary derived
objects follows separately from naturality and K-flat resolutions. -/
theorem completedPullbackTensor_signed_representatives {X Y : Scheme.{u}}
    (f : X ⟶ Y) (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) Q) :
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    (pullbackTensorSequenceDerived l E f).map
      ((pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y)
        (pullbackTensorCalculus l E Y).systemClosed
        (pullbackTensorCalculus l E Y).systemTensorModel).hom.app (M,N)) ≫
      (pullbackTensorSystemComparison l E f).hom.app (N,M) =
    (pullbackTensorSystemComparison l E f).hom.app (M,N) ≫
      (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        (pullbackTensorCalculus l E X).systemClosed
        (pullbackTensorCalculus l E X).systemTensorModel).hom.app
          ((pullbackTensorSequenceDerived l E f).obj M,
            (pullbackTensorSequenceDerived l E f).obj N) := by
  unfold pullbackTensorSequenceDerived
  let L := pullbackTensorSequenceInverse l E f
  let F := L.mapDerivedCategory
  let C := L.mapHomologicalComplex (.up ℤ)
  let δ := L.mapDerivedCategoryFactors
  let α := pullbackTensorSystemComparison l E f
  let TX := (pullbackTensorCalculus l E X).systemClosed.tensor
  let βY := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y)
    (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E Y).systemTensorModel
  let βX := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)
    (pullbackTensorCalculus l E X).systemClosed
    (pullbackTensorCalculus l E X).systemTensorModel
  let σY := pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y) P Q
  let σX := pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X) (C.obj P) (C.obj Q)
  let κ := (pullbackTensorSequenceCochain l E f).app (P,Q)
  let κ' := (pullbackTensorSequenceCochain l E f).app (Q,P)
  have hP' := pullbackTensorSequenceGood l E f P hP
  have hQ' := pullbackTensorSequenceGood l E f Q hQ
  let r := pullbackTensorSystemModel l E Y P Q hP hQ
  let s := pullbackTensorSystemModel l E Y Q P hQ hP
  let r' := pullbackTensorSystemModel l E X (C.obj P) (C.obj Q) hP' hQ'
  let s' := pullbackTensorSystemModel l E X (C.obj Q) (C.obj P) hQ' hP'
  let e := δ.app _ ≪≫ DerivedCategory.Q.mapIso κ
  let e' := δ.app _ ≪≫ DerivedCategory.Q.mapIso κ'
  have hσY : DerivedCategory.Q.map σY.hom ≫ s.hom =
      r.hom ≫ βY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
    dsimp only [σY, s, r, pullbackTensorSystemModel]
    unfold βY pullbackTensorBraiding
    exact
      (pullbackTensorBraiding_existsUnique
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)
      (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E Y).systemTensorModel).exists.choose_spec P Q hP hQ
  have hσX : DerivedCategory.Q.map σX.hom ≫ s'.hom =
      r'.hom ≫ βX.hom.app (DerivedCategory.Q.obj (C.obj P),
        DerivedCategory.Q.obj (C.obj Q)) := by
    dsimp only [σX, s', r', pullbackTensorSystemModel]
    unfold βX pullbackTensorBraiding
    exact
      (pullbackTensorBraiding_existsUnique
      (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X)
      (pullbackTensorCalculus l E X).systemClosed
      (pullbackTensorCalculus l E X).systemTensorModel).exists.choose_spec
        (C.obj P) (C.obj Q) hP' hQ'
  have hn : F.map (DerivedCategory.Q.map σY.hom) ≫ e'.hom =
      e.hom ≫ DerivedCategory.Q.map σX.hom := by
    change F.map (DerivedCategory.Q.map σY.hom) ≫ δ.hom.app _ ≫
        DerivedCategory.Q.map κ'.hom =
      (δ.hom.app _ ≫ DerivedCategory.Q.map κ.hom) ≫ DerivedCategory.Q.map σX.hom
    have hδ := δ.hom.naturality σY.hom
    dsimp only [Functor.comp_map] at hδ
    simp only [Category.assoc]
    rw [← Category.assoc, hδ]
    simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
    apply congrArg (fun v ↦ δ.hom.app _ ≫ DerivedCategory.Q.map v)
    exact coherentSignedTotal l E f P Q
  have hr : F.map r.hom ≫ α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      TX.map (Prod.mkHom (δ.hom.app P) (δ.hom.app Q)) = e.hom ≫ r'.hom := by
    dsimp only [F, L, r, TX, δ, e, r', κ, α, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    unfold pullbackTensorSystemComparison pullbackTensorUniqueChoice
    simpa only [pullbackTensorSequenceDerived, Category.assoc] using
      (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec P Q hP hQ
  have hs : F.map s.hom ≫ α.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
      TX.map (Prod.mkHom (δ.hom.app Q) (δ.hom.app P)) = e'.hom ≫ s'.hom := by
    dsimp only [F, L, s, TX, δ, e', s', κ', α, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    unfold pullbackTensorSystemComparison pullbackTensorUniqueChoice
    simpa only [pullbackTensorSequenceDerived, Category.assoc] using
      (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec Q P hQ hP
  exact normalizedSignedSquare F TX βX
    (DerivedCategory.Q.map σY.hom) (DerivedCategory.Q.map σX.hom)
    r s r' s' e e' (βY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (α.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
    (δ.app P) (δ.app Q) hσY hσX hn hr hs

end WeilConjectures
