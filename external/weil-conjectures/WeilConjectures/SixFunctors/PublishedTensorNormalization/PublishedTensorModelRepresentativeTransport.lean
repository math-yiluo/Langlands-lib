/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryTensorPullbackData
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.UnitNormalizedCochainTensor
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! Tensor-model representative rectangles and transport.
Source: Stacks 03D3, 03EL and 07A4.
(blueprint: lem-sf-tensor-model-representative-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard WeilConjectures.CoefficientClosedStructure.tensor
namespace WeilConjectures
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Functor
open WeilConjectures.SemilinearSections
namespace PublishedTensorNormalization
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
section
variable {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K]
  (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf K CommRingCat.{max c v r})
  (phi : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{max c v r} J K).obj S)
  (F : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} K S)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (adj : F ⊣ SheafOfModules.pushforward.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map phi))
  (A : WeilConjectures.SemilinearSections.Closed.{c, v, r} J R)
  (B : WeilConjectures.SemilinearSections.Closed.{c, v, r} K S)
  (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} K S B)
  (mu : A.tensor ⋙ F.mapDerivedCategory ≅
    (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor)
  (M : TensorComparisonModel.{c, v, r} J K R S F A B TA TB mu)
  (hiso : ∀ P Q, IsIso (M.chain P Q))
  (e : totalTensor.{c, v, r} J R ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    ((F.mapHomologicalComplex (.up ℤ)).prod
      (F.mapHomologicalComplex (.up ℤ))) ⋙ totalTensor.{c, v, r} K S)
  (ho : ∀ (M' N' : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) (V : C)
    (x : M'.val.obj (op V)) (y : N'.val.obj (op V)),
    ((M.ordinary M' N').hom.val.app (op (U.obj V)))
      ((adj.unit.app (ordinaryTensor.{c, v, r} J R M' N')).val.app (op V)
        (tensorSectionAtSize J R M' N' (op V) x y)) =
      tensorSectionAtSize K S (F.obj M') (F.obj N') (op (U.obj V))
        ((adj.unit.app M').val.app (op V) x)
        ((adj.unit.app N').val.app (op V) y))
  (he : ∀ (P Q : CochainComplex (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : C)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
    ((e.hom.app (P, Q)).f k).val.app (op (U.obj V))
      ((adj.unit.app (((totalTensor.{c, v, r} J R).obj (P, Q)).X k)).val.app (op V)
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k h (op V) x y)) =
      coefficientTensorGenerator.{r, c, v} K S
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k h (op (U.obj V))
        ((adj.unit.app (P.X p)).val.app (op V) x)
        ((adj.unit.app (Q.X q)).val.app (op V) y))

include hiso ho he in
/-- The unit formula and the model summand formula determine inverse chain maps. -/
private theorem chain_eq
    (P Q : CochainComplex (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) :
    M.chain P Q = e.inv.app (P, Q) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  have := hiso P Q
  suffices hi : (asIso (M.chain P Q)).inv = e.hom.app (P, Q) by
    have hh : (asIso (M.chain P Q)).symm = e.app (P, Q) := Iso.ext hi
    exact congrArg Iso.inv hh
  apply HomologicalComplex.hom_ext
  intro k
  apply (adj.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{c, v, r}
    (J := J) (R := R) P Q k _
  intro p q h W x y
  let i := tensorSummand.{c, v, r} J R P Q p q k h
  let i' := tensorSummand.{c, v, r} K S
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k h
  let z := (HomologicalComplex.eval _ (.up ℤ) k).mapIso (asIso (M.chain P Q))
  have hz : i' ≫ z.hom = (M.ordinary (P.X p) (Q.X q)).inv ≫ F.map i :=
    M.summand P Q p q k h
  have hi : F.map i ≫ z.inv = (M.ordinary (P.X p) (Q.X q)).hom ≫ i' :=
    WeilConjectures.SemilinearSections.normalizedTensor_inverse_square
      (M.ordinary (P.X p) (Q.X q)) z hz
  have hu := congrArg (fun a ↦ a.val.app W
    (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) W x y))
    (adj.unit.naturality i)
  have hh := congrArg (fun a ↦ a.val.app (op (U.obj W.unop))
    ((adj.unit.app (ordinaryTensor.{c, v, r} J R (P.X p) (Q.X q))).val.app W
      (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) W x y))) hi
  change z.inv.val.app (op (U.obj W.unop))
    ((adj.unit.app (((totalTensor.{c, v, r} J R).obj (P, Q)).X k)).val.app W
      (i.val.app W
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) W x y))) = _
  change (adj.unit.app _).val.app W
    (i.val.app W (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) W x y)) =
    (F.map i).val.app (op (U.obj W.unop))
      ((adj.unit.app (ordinaryTensor.{c, v, r} J R (P.X p) (Q.X q))).val.app W
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) W x y)) at hu
  erw [hu]
  exact (hh.trans (congrArg (i'.val.app (op (U.obj W.unop)))
    (ho (P.X p) (Q.X q) W.unop x y))).trans (he P Q p q k h W.unop x y).symm

include hiso ho he in
/-- Invert the model rectangle after identifying its chain map. -/
private theorem model_forward
    (P Q : CochainComplex (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (flatP : flatTerms.{c, v, r} J R P) (flatQ : flatTerms.{c, v, r} J R Q) :
    F.mapDerivedCategory.map (tensorModelIso.{c, v, r} J R A TA P Q hP hQ).hom ≫
      mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      B.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
        (F.mapDerivedCategoryFactors.hom.app Q)) =
    F.mapDerivedCategoryFactors.hom.app ((totalTensor.{c, v, r} J R).obj (P, Q)) ≫
      DerivedCategory.Q.map (e.hom.app (P, Q)) ≫
      (tensorModelIso.{c, v, r} K S B TB
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q)
        (M.kflat P hP flatP) (M.kflat Q hQ flatQ)).hom := by
  have hm := M.derived P Q hP hQ flatP flatQ
  rw [chain_eq J K U R S phi F adj A B TA TB mu M hiso e ho he P Q] at hm
  let a := F.mapDerivedCategory.mapIso (tensorModelIso.{c, v, r} J R A TA P Q hP hQ)
  let b := mu.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  let c' := B.tensor.mapIso (Iso.prod (F.mapDerivedCategoryFactors.app P)
    (F.mapDerivedCategoryFactors.app Q))
  let d := tensorModelIso.{c, v, r} K S B TB
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q)
    (M.kflat P hP flatP) (M.kflat Q hQ flatQ)
  have hm' : d.hom ≫ c'.inv ≫ b.inv ≫ a.inv ≫
      F.mapDerivedCategoryFactors.hom.app ((totalTensor.{c, v, r} J R).obj (P, Q)) =
      (DerivedCategory.Q.mapIso (e.app (P, Q))).inv := hm
  have hh := congrArg (fun z ↦ a.hom ≫ b.hom ≫ c'.hom ≫ d.inv ≫ z ≫
    (DerivedCategory.Q.mapIso (e.app (P, Q))).hom ≫ d.hom) hm'
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id] at hh
  exact hh.symm

end

/-- Transport the forward tensor-model rectangle along equal ring maps and exact inverse images.
Source: Stacks 03D3, 03EL and 07A4.
(blueprint: lem-sf-tensor-model-representative-transport).

Proof: invert the ordinary model summand square. Adjunction-unit naturality and
ordinary pure-tensor normalization identify the inverse chain comparison with the
unit-normalized forward cochain comparison, by adjunction injectivity and pure
extensionality on all total summands. Substitute this equality into the derived
model equation and cancel the invertible model, tensor and localization factors.
Finally use equality induction on the coefficient map, functor and specified
adjunction, after which the eqToIso transport is the identity. -/
private theorem model_transport {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K]
  (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf K CommRingCat.{max c v r})
  (phi psi : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{max c v r} J K).obj S)
  (hphi : phi = psi)
  (F G : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} K S)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (hF : F = G)
  (adjF : F ⊣ SheafOfModules.pushforward.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map phi))
  (adjG : G ⊣ SheafOfModules.pushforward.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map psi))
  (hadj : HEq adjF adjG)
  (A : WeilConjectures.SemilinearSections.Closed.{c, v, r} J R)
  (B : WeilConjectures.SemilinearSections.Closed.{c, v, r} K S)
  (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} K S B)
  (mu : A.tensor ⋙ G.mapDerivedCategory ≅
    (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ B.tensor)
  (M : TensorComparisonModel.{c, v, r} J K R S G A B TA TB mu)
  (hiso : ∀ P Q, IsIso (M.chain P Q))
  (e : totalTensor.{c, v, r} J R ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    ((F.mapHomologicalComplex (.up ℤ)).prod
      (F.mapHomologicalComplex (.up ℤ))) ⋙ totalTensor.{c, v, r} K S)
  (ho : ∀ (M' N' : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) (V : C)
    (x : M'.val.obj (op V)) (y : N'.val.obj (op V)),
    ((M.ordinary M' N').hom.val.app (op (U.obj V)))
      ((adjG.unit.app (ordinaryTensor.{c, v, r} J R M' N')).val.app (op V)
        (tensorSectionAtSize J R M' N' (op V) x y)) =
      tensorSectionAtSize K S (G.obj M') (G.obj N') (op (U.obj V))
        ((adjG.unit.app M').val.app (op V) x)
        ((adjG.unit.app N').val.app (op V) y))
  (he : ∀ (P Q : CochainComplex (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : C)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
    ((e.hom.app (P, Q)).f k).val.app (op (U.obj V))
      ((adjF.unit.app (((totalTensor.{c, v, r} J R).obj (P, Q)).X k)).val.app (op V)
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k h (op V) x y)) =
      coefficientTensorGenerator.{r, c, v} K S
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k h (op (U.obj V))
        ((adjF.unit.app (P.X p)).val.app (op V) x)
        ((adjF.unit.app (Q.X q)).val.app (op V) y))
  (d : F.mapDerivedCategory ≅ G.mapDerivedCategory)
  (hd : ∃ h : F.mapDerivedCategory = G.mapDerivedCategory, d = eqToIso h)
  (P Q : CochainComplex (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
  (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
  (flatP : flatTerms.{c, v, r} J R P) (flatQ : flatTerms.{c, v, r} J R Q)
  (hFP : CochainComplex.IsKFlatIndependentCoefficients (J := K) (R := S)
    ((F.mapHomologicalComplex (.up ℤ)).obj P))
  (hFQ : CochainComplex.IsKFlatIndependentCoefficients (J := K) (R := S)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q)) :
  F.mapDerivedCategory.map (tensorModelIso.{c, v, r} J R A TA P Q hP hQ).hom ≫
    (isoWhiskerLeft A.tensor d ≪≫ mu ≪≫
      isoWhiskerRight (NatIso.prod d d).symm B.tensor).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
    B.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
      (F.mapDerivedCategoryFactors.hom.app Q)) =
  F.mapDerivedCategoryFactors.hom.app ((totalTensor.{c, v, r} J R).obj (P, Q)) ≫
    DerivedCategory.Q.map (e.hom.app (P, Q)) ≫
    (tensorModelIso.{c, v, r} K S B TB
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) hFP hFQ).hom := by
  subst psi
  subst G
  have ha : adjF = adjG := eq_of_heq hadj
  subst adjG
  rcases hd with ⟨h, rfl⟩
  have hd : eqToIso h = Iso.refl F.mapDerivedCategory := rfl
  have hp : NatIso.prod (Iso.refl F.mapDerivedCategory) (Iso.refl F.mapDerivedCategory) =
      Iso.refl _ := rfl
  rw [hd, hp]
  simp only [Functor.isoWhiskerLeft_refl, Iso.refl_symm,
    Functor.isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_refl]
  exact model_forward J K U R S phi F adjF A B TA TB mu M hiso e ho he
    P Q hP hQ flatP flatQ

/-- The representative rectangle expressed through named presentation wrappers.
Source: Stacks 03D3, 03EL and 07A4.
(blueprint: lem-sf-tensor-model-representative-transport).

Proof: substitute the equal total complexes and derived functor. Each heterogeneous
model, comparison, localization-factor and cochain-map equality becomes an ordinary
equality. Substitute them and apply the generic transported model rectangle. -/
theorem model_transport_named {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K]
  (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf K CommRingCat.{max c v r})
  (phi psi : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{max c v r} J K).obj S)
  (hphi : phi = psi)
  (F G : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} K S)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (hF : F = G)
  (adjF : F ⊣ SheafOfModules.pushforward.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map phi))
  (adjG : G ⊣ SheafOfModules.pushforward.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map psi))
  (hadj : HEq adjF adjG)
  (A : WeilConjectures.SemilinearSections.Closed.{c, v, r} J R)
  (B : WeilConjectures.SemilinearSections.Closed.{c, v, r} K S)
  (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} K S B)
  (mu : A.tensor ⋙ G.mapDerivedCategory ≅
    (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ B.tensor)
  (M : TensorComparisonModel.{c, v, r} J K R S G A B TA TB mu)
  (hiso : ∀ P Q, IsIso (M.chain P Q))
  (e : totalTensor.{c, v, r} J R ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    ((F.mapHomologicalComplex (.up ℤ)).prod
      (F.mapHomologicalComplex (.up ℤ))) ⋙ totalTensor.{c, v, r} K S)
  (ho : ∀ (M' N' : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) (V : C)
    (x : M'.val.obj (op V)) (y : N'.val.obj (op V)),
    ((M.ordinary M' N').hom.val.app (op (U.obj V)))
      ((adjG.unit.app (ordinaryTensor.{c, v, r} J R M' N')).val.app (op V)
        (tensorSectionAtSize J R M' N' (op V) x y)) =
      tensorSectionAtSize K S (G.obj M') (G.obj N') (op (U.obj V))
        ((adjG.unit.app M').val.app (op V) x)
        ((adjG.unit.app N').val.app (op V) y))
  (he : ∀ (P Q : CochainComplex (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : C)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
    ((e.hom.app (P, Q)).f k).val.app (op (U.obj V))
      ((adjF.unit.app (((totalTensor.{c, v, r} J R).obj (P, Q)).X k)).val.app (op V)
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k h (op V) x y)) =
      coefficientTensorGenerator.{r, c, v} K S
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k h (op (U.obj V))
        ((adjF.unit.app (P.X p)).val.app (op V) x)
        ((adjF.unit.app (Q.X q)).val.app (op V) y))
  (d : F.mapDerivedCategory ≅ G.mapDerivedCategory)
  (hd : ∃ h : F.mapDerivedCategory = G.mapDerivedCategory, d = eqToIso h)
  (P Q : CochainComplex (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
  (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
  (flatP : flatTerms.{c, v, r} J R P) (flatQ : flatTerms.{c, v, r} J R Q)
  (hFP : CochainComplex.IsKFlatIndependentCoefficients (J := K) (R := S)
    ((F.mapHomologicalComplex (.up ℤ)).obj P))
  (hFQ : CochainComplex.IsKFlatIndependentCoefficients (J := K) (R := S)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q))
  (FD : SemilinearSections.D.{c, v, max c v r} J R ⥤
    SemilinearSections.D.{c, v, max c v r} K S)
  (hFD : FD = F.mapDerivedCategory)
  (Z : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
  (hZ : Z = (totalTensor.{c, v, r} J R).obj (P, Q))
  (Z' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} K S) ℤ)
  (hZ' : Z' = (totalTensor.{c, v, r} K S).obj
    (((F.mapHomologicalComplex (.up ℤ)).obj P),
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
  (sm : DerivedCategory.Q.obj Z ≅ A.tensor.obj
    (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
  (hsm : HEq sm (tensorModelIso.{c, v, r} J R A TA P Q hP hQ))
  (tm : DerivedCategory.Q.obj Z' ≅ B.tensor.obj
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P),
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
  (htm : HEq tm (tensorModelIso.{c, v, r} K S B TB
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q) hFP hFQ))
  (m' : A.tensor ⋙ FD ≅ (FD.prod FD) ⋙ B.tensor)
  (hm' : HEq m' (isoWhiskerLeft A.tensor d ≪≫ mu ≪≫
    isoWhiskerRight (NatIso.prod d d).symm B.tensor))
  (a : DerivedCategory.Q ⋙ FD ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (ha : HEq a F.mapDerivedCategoryFactors)
  (e' : (F.mapHomologicalComplex (.up ℤ)).obj Z ⟶ Z')
  (he' : HEq e' (e.hom.app (P, Q))) :
  FD.map sm.hom ≫ m'.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
    B.tensor.map (Prod.mkHom (a.hom.app P) (a.hom.app Q)) =
    a.hom.app Z ≫ DerivedCategory.Q.map e' ≫ tm.hom := by
  subst FD
  subst Z
  subst Z'
  have hs : sm = tensorModelIso.{c, v, r} J R A TA P Q hP hQ := eq_of_heq hsm
  subst sm
  have ht : tm = tensorModelIso.{c, v, r} K S B TB
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) hFP hFQ := eq_of_heq htm
  subst tm
  have hm : m' = isoWhiskerLeft A.tensor d ≪≫ mu ≪≫
      isoWhiskerRight (NatIso.prod d d).symm B.tensor := eq_of_heq hm'
  subst m'
  have haa : a = F.mapDerivedCategoryFactors := eq_of_heq ha
  subst a
  have hee : e' = e.hom.app (P, Q) := eq_of_heq he'
  subst e'
  exact model_transport J K U R S phi psi hphi F G hF adjF adjG hadj
    A B TA TB mu M hiso e ho he d hd P Q hP hQ flatP flatQ hFP hFQ

end PublishedTensorNormalization
end WeilConjectures
