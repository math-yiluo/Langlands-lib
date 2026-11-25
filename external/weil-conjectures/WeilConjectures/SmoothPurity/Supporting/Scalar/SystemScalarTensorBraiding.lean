/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorSignedRepresentatives
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorCoherentConstruction

/-! # Scalar extension preserves the signed symmetry of coherent systems

Source: Stacks Project, Tag 07A4 and the Koszul sign rules, Tag 0FNG.
(blueprint: lem-pur-system-scalar-tensor-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard pullbackTensorCalculus
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  integralComparisonSequenceScalarModel
  pullbackTensorBraiding pullbackTensorSignedTotal coefficientTotalTensor
attribute [local implicit_reducible] pullbackTensorSwap
  integralComparisonDerivedSequenceScalar
  ScalarExtensionTower.tensor
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

open Opposite ScalarExtensionTower

section Chain
variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

private theorem sigmaDegree (P Q : Complex l E W) (p q k : ℤ) (h : p + q = k)
    (V : (ℕ × W.ProEt)ᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    ((((comparisons l).sigma E L ι W).hom.app (P, Q)).f k).val.app V (
      integralComparisonSequenceTensorSection l E L ι W
        (((tensor l E W).obj (P, Q)).X k) V 1
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q p q k h V x y)) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W)
        ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q k h V
        (integralComparisonSequenceTensorSection l E L ι W (P.X p) V 1 x)
        (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y) := by
  subst k
  exact (comparisons l).sigma_formula E L ι W P Q p q V 1 x y

-- Section maps pass through the scalar adjunction and the total-tensor sheafification.
private theorem scalarSignedTotal (P Q : Complex l E W) :
    (scalar l E L ι W).map
        (pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q).hom ≫
      ((comparisons l).sigma E L ι W).hom.app (Q, P) =
    ((comparisons l).sigma E L ι W).hom.app (P, Q) ≫
      (pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W)
        ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q)).hom := by
  let F := (integralComparisonSequenceScalarModel l E L ι W).E
  let G := SheafOfModules.restrictScalars ((sheafCompose
    (coefficientSequenceTopology (ProEt.topology W))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralComparisonSequenceScalarMap l E L ι W))
  let adj := scalar_adj l E L ι W
  let κ := ((comparisons l).sigma E L ι W)
  let σE := pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) P Q
  let σL := pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l L W)
    ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q)
  have hσE := (pullbackTensorSignedTotal_existsUnique
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) P Q).exists.choose_spec
  have hσL := (pullbackTensorSignedTotal_existsUnique
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l L W)
    ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q)).exists.choose_spec
  apply HomologicalComplex.hom_ext
  intro k
  change F.map (σE.hom.f k) ≫ (κ.hom.app (Q, P)).f k =
    (κ.hom.app (P, Q)).f k ≫ σL.hom.f k
  apply (adj.homEquiv _ _).injective
  change adj.unit.app _ ≫ G.map
      (F.map (σE.hom.f k) ≫ (κ.hom.app (Q, P)).f k) =
    adj.unit.app _ ≫ G.map ((κ.hom.app (P, Q)).f k ≫ σL.hom.f k)
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality (σE.hom.f k)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu]
  apply total_tensor_sections_ext l E W P Q k
  intro p q hpq V x y
  subst k
  change ((κ.hom.app (Q, P)).f (p + q)).val.app V
      ((adj.unit.app _).val.app V ((σE.hom.f (p + q)).val.app V
        (generator l E W P Q p q V x y))) =
    (σL.hom.f (p + q)).val.app V
      (((κ.hom.app (P, Q)).f (p + q)).val.app V
        ((adj.unit.app _).val.app V (generator l E W P Q p q V x y)))
  have hE : (σE.hom.f (p + q)).val.app V
      (generator l E W P Q p q V x y) =
    (p * q).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) Q P q p (p + q)
      (add_comm q p) V y x := by
    dsimp only [σE]
    unfold pullbackTensorSignedTotal
    exact hσE p q (p + q) rfl V x y
  have hPQ : ((κ.hom.app (P, Q)).f (p + q)).val.app V
      ((adj.unit.app _).val.app V (generator l E W P Q p q V x y)) =
    generator l L W ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q V
      ((adj.unit.app (P.X p)).val.app V x)
      ((adj.unit.app (Q.X q)).val.app V y) := by
    simpa only [adj, scalar_adj, sequenceScalarAdjunction_unit] using
      (comparisons l).sigma_formula E L ι W P Q p q V 1 x y
  have hQP : ((κ.hom.app (Q, P)).f (p + q)).val.app V
      ((adj.unit.app _).val.app V (coefficientTensorGenerator.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) Q P q p (p + q)
      (add_comm q p) V y x)) =
    coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l L W)
      ((scalar l E L ι W).obj Q) ((scalar l E L ι W).obj P) q p (p + q)
      (add_comm q p) V ((adj.unit.app (Q.X q)).val.app V y)
      ((adj.unit.app (P.X p)).val.app V x) := by
    simpa only [κ, adj, scalar_adj, sequenceScalarAdjunction_unit] using
      sigmaDegree l E L ι W Q P q p (p + q) (add_comm q p) V y x
  exact signedSectionSquare
    ((σE.hom.f (p + q)).val.app V).hom.toAddMonoidHom
    ((adj.unit.app (((tensor l E W).obj (Q, P)).X (p + q))).val.app V).hom.toAddMonoidHom
    (((κ.hom.app (Q, P)).f (p + q)).val.app V).hom.toAddMonoidHom
    ((adj.unit.app (((tensor l E W).obj (P, Q)).X (p + q))).val.app V).hom.toAddMonoidHom
    (((κ.hom.app (P, Q)).f (p + q)).val.app V).hom.toAddMonoidHom
    ((σL.hom.f (p + q)).val.app V).hom.toAddMonoidHom
    _ _ _ _ (p * q).negOnePow hE hQP hPQ (by
      dsimp only [σL]
      unfold pullbackTensorSignedTotal
      exact hσL p q (p + q) rfl V _ _)

end Chain

/-- The normalized whole-system scalar tensorator preserves signed symmetry.
No completed tensor, constructible scalar comparison or integral braiding occurs.

Source: Stacks, more-algebra.tex, item-flip-tensor-product; Stacks 07A4, scalar tensor comparison;
step 2 of lem-pur-integral-braiding-scalar-extension-square-reduced.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof: take simultaneous flat-term K-flat representatives P,Q on the ringed
sequence site. By DerivedSigmaModel the derived scalar tensorator is the
localization of the strict scalar tensorator, conjugated by the fixed tensor
model isomorphisms and scalar counits. By pullbackTensorBraiding_existsUnique
the system braidings are the localizations of the signed total swaps with those
same tensor models. On a homogeneous local tensor of degrees p,q the two strict
routes both interchange the two inputs and multiply by (-1)^(pq). Scalar
coefficients have degree zero, and tensor balancing moves the coefficient to
the other factor, so the two routes agree for every scalar. These generators
span the sheafified tensor and each total-complex coproduct summand. Thus the
strict chain maps agree, including all sequence-site transitions. Localize and
cancel the tensor model maps and scalar counits. Naturality transports the
equality from the representatives to arbitrary system objects. Zero objects,
identity coefficient maps, degree-zero inputs and ramification satisfy the same
formula; no separate derived evaluations are used to detect equality. -/
theorem systemScalarTensorBraiding
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : coefficientSequenceDerived l E W) :
    let H := integralComparisonDerivedSequenceScalar l E L ι W
    let σ := ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
    H.map ((pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (pullbackTensorCalculus l E W).systemClosed
        (pullbackTensorCalculus l E W).systemTensorModel).hom.app (M, N)) ≫
      σ.hom.app (N, M) =
    σ.hom.app (M, N) ≫
      (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W)
        (pullbackTensorCalculus l L W).systemClosed
        (pullbackTensorCalculus l L W).systemTensorModel).hom.app
          (H.obj M, H.obj N) := by
  let SE := pullbackTensorCalculus l E W
  let SL := pullbackTensorCalculus l L W
  let F := integralComparisonDerivedSequenceScalar l E L ι W
  let C := scalar l E L ι W
  let δ := integralComparisonSequenceScalarModel l E L ι W
  let α := derivedSigma l E L ι W SE SL
  let βE := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) SE.systemClosed SE.systemTensorModel
  let βL := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l L W) SL.systemClosed SL.systemTensorModel
  let a : SE.systemClosed.tensor ⋙ F ⟶
      pullbackTensorSwap _ ⋙ F.prod F ⋙ SL.systemClosed.tensor :=
    Functor.whiskerRight βE.hom F ≫
      Functor.whiskerLeft (pullbackTensorSwap _) α.hom
  let b : SE.systemClosed.tensor ⋙ F ⟶
      pullbackTensorSwap _ ⋙ F.prod F ⋙ SL.systemClosed.tensor :=
    α.hom ≫ Functor.whiskerLeft (F.prod F) βL.hom
  have res (X : coefficientSequenceDerived l E W) :
      ∃ P : Complex l E W, Good l E W P ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let q := DerivedCategory.Q (C := coefficientSequenceModules l E W)
    obtain ⟨P, f, hP, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) (q.objPreimage X)
    have : QuasiIso f := hf
    refine ⟨P, ⟨hP, fun n ↦ ?_⟩, ⟨asIso (q.map f) ≪≫ q.objObjPreimageIso X⟩⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (coefficientSequenceCommRingSheaf l E W) (P.X n)).symm (hflat n)
  have hab : a = b := tensorNatTrans_ext_resolving DerivedCategory.Q (Good l E W)
    res a b (by
      intro P Q hP hQ
      have hα := (derivedSigma_existsUnique l E L ι W SE SL).exists.choose_spec
      change DerivedSigmaModel l E L ι W SE SL α at hα
      unfold DerivedSigmaModel at hα
      obtain ⟨hP', hQ', hr⟩ := hα P Q hP hQ
      obtain ⟨_, _, hs⟩ := hα Q P hQ hP
      have : IsIso (δ.ε.app P) := δ.computes P hP.1
      have : IsIso (δ.ε.app Q) := δ.computes Q hQ.1
      let σE := pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) P Q
      let σL := pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W) (C.obj P) (C.obj Q)
      let r := SE.systemTensorModel.iso _ _ _ P Q hP.1 hQ.1
      let s := SE.systemTensorModel.iso _ _ _ Q P hQ.1 hP.1
      let r' := SL.systemTensorModel.iso _ _ _ (C.obj P) (C.obj Q) hP'.1 hQ'.1
      let s' := SL.systemTensorModel.iso _ _ _ (C.obj Q) (C.obj P) hQ'.1 hP'.1
      have : IsIso (δ.ε.app ((tensor l E W).obj (P, Q))) := δ.computes _
        (coefficientTotalTensor_isKFlat _ _ P Q hP.1 hQ.1)
      have : IsIso (δ.ε.app ((tensor l E W).obj (Q, P))) := δ.computes _
        (coefficientTotalTensor_isKFlat _ _ Q P hQ.1 hP.1)
      let e := asIso (δ.ε.app ((tensor l E W).obj (P, Q))) ≪≫
        DerivedCategory.Q.mapIso (((comparisons l).sigma E L ι W).app (P, Q))
      let e' := asIso (δ.ε.app ((tensor l E W).obj (Q, P))) ≪≫
        DerivedCategory.Q.mapIso (((comparisons l).sigma E L ι W).app (Q, P))
      have hσE : DerivedCategory.Q.map σE.hom ≫ s.hom =
          r.hom ≫ βE.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
        dsimp only [σE, s, r, βE]
        unfold pullbackTensorBraiding
        exact (pullbackTensorBraiding_existsUnique _ _ SE.systemClosed SE.systemTensorModel
          ).exists.choose_spec P Q hP.1 hQ.1
      have hσL : DerivedCategory.Q.map σL.hom ≫ s'.hom =
          r'.hom ≫ βL.hom.app (DerivedCategory.Q.obj (C.obj P),
            DerivedCategory.Q.obj (C.obj Q)) := by
        dsimp only [σL, s', r', βL]
        unfold pullbackTensorBraiding
        exact (pullbackTensorBraiding_existsUnique _ _ SL.systemClosed SL.systemTensorModel
          ).exists.choose_spec (C.obj P) (C.obj Q) hP'.1 hQ'.1
      have hn : F.map (DerivedCategory.Q.map σE.hom) ≫ e'.hom =
          e.hom ≫ DerivedCategory.Q.map σL.hom := by
        have hδ := δ.ε.naturality σE.hom
        dsimp only [Functor.comp_map] at hδ
        change _ ≫ (δ.ε.app _ ≫ DerivedCategory.Q.map _) =
          (δ.ε.app _ ≫ DerivedCategory.Q.map _) ≫ _
        change F.map (DerivedCategory.Q.map σE.hom) ≫ δ.ε.app _ = _ at hδ
        rw [← Category.assoc, hδ]
        simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
        exact congrArg (fun v ↦ δ.ε.app _ ≫ DerivedCategory.Q.map v)
          (scalarSignedTotal l E L ι W P Q)
      exact normalizedSignedSquare F SL.systemClosed.tensor βL
        (DerivedCategory.Q.map σE.hom) (DerivedCategory.Q.map σL.hom)
        r s r' s' e e' (βE.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
        (α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
        (α.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
        (asIso (δ.ε.app P)) (asIso (δ.ε.app Q)) hσE hσL hn
        (by
          exact hr.trans (Category.assoc _ _ _).symm)
        (by
          exact hs.trans (Category.assoc _ _ _).symm))
  exact NatTrans.congr_app hab (M, N)

end WeilConjectures
