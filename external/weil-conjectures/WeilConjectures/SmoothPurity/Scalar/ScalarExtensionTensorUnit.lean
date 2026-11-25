/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-! # Identity scalar extension and the signed tensor

Source: Stacks Project, Modules on Sites, Tag 03EL; Cohomology on Sites, Tag 07A4
(blueprint: lem-pur-scalar-tensor-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
universe u c v r
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : Scheme.{u})

local instance (priority := 3000) : EssentiallySmall.{u + 1} (ℕ × W.ProEt) :=
  coefficientSequenceEssentiallySmall.{u, 0} W

local instance (priority := 3000) :
    (integralComparisonSequenceScalarModel.{u, u}
      l E E (AlgHom.id ℚ_[l] E) W).E.Additive :=
  (integralComparisonSequenceScalarModel.{u, u}
    l E E (AlgHom.id ℚ_[l] E) W).additive

attribute [local irreducible] integralComparisonSequenceScalarModel

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

open CategoryTheory.MonoidalCategory

private def tensorSection
    (M N : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V) : (M ⊗ N).val.obj V :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app V
    (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf.{u, u} l E W)).obj)).unit.app
          (M.val ⊗ N.val)).app V
            (x ⊗ₜ[(coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V] y))

private theorem tensor_sections_ext
    (M N H : coefficientSequenceModules.{u, u} l E W)
    {f g : M ⊗ N ⟶ H}
    (h : ∀ (V : (ℕ × W.ProEt)ᵒᵖ) (x : M.val.obj V) (y : N.val.obj V),
      f.val.app V (tensorSection l E W M N V x y) =
        g.val.app V (tensorSection l E W M N V x y)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf.{u, u} l E W)).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h V x y

private theorem tensor_iso_naturality
    {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1})
    [(J.W.inverseImage (PresheafOfModules.toPresheaf.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).IsMonoidal]
    {M M' N N' : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification.{u + 1}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
            (f.val ⊗ₘ g.val) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have hf := adj.counit.naturality f
  have hg := adj.counit.naturality g
  dsimp at hf hg
  simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    tensorIso_inv, Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural]
  simp only [← Category.assoc]
  congr 1
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  · simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
    rw [← Category.assoc, ← hf, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rfl
  · simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
    rw [← Category.assoc, ← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rfl

private theorem tensorSection_map
    {M M' N N' : coefficientSequenceModules.{u, u} l E W} (f : M ⟶ M') (g : N ⟶ N')
    (V : (ℕ × W.ProEt)ᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (f ⊗ₘ g).val.app V (tensorSection l E W M N V x y) =
      tensorSection l E W M' N' V (f.val.app V x) (g.val.app V y) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf.{u, u} l E W)).obj)
  let S := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf.{u, u} l E W)).obj)
  have hi : (SheafOfModules.tensorObjIsoSheafification M N).inv ≫ (f ⊗ₘ g) =
      S.map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensor_iso_naturality
        (coefficientSequenceCommRingSheaf.{u, u} l E W),
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hn := adj.unit.naturality (f.val ⊗ₘ g.val)
  have hp : adj.unit.app (M.val ⊗ N.val) ≫
      (SheafOfModules.tensorObjIsoSheafification M N).inv.val ≫ (f ⊗ₘ g).val =
    (f.val ⊗ₘ g.val) ≫ adj.unit.app (M'.val ⊗ N'.val) ≫
      (SheafOfModules.tensorObjIsoSheafification M' N').inv.val := by
    have hv := congrArg SheafOfModules.Hom.val hi
    change (SheafOfModules.tensorObjIsoSheafification M N).inv.val ≫ (f ⊗ₘ g).val =
      (S.map (f.val ⊗ₘ g.val)).val ≫
        (SheafOfModules.tensorObjIsoSheafification M' N').inv.val at hv
    change (f.val ⊗ₘ g.val) ≫ adj.unit.app (M'.val ⊗ N'.val) =
      adj.unit.app (M.val ⊗ N.val) ≫ (S.map (f.val ⊗ₘ g.val)).val at hn
    erw [hv, ← Category.assoc, ← hn, Category.assoc]
  exact congrArg (fun t ↦ t.app V
    (x ⊗ₜ[(coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V] y)) hp

private theorem total_tensor_sections_ext
    (P Q : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    (n : ℤ) (H : coefficientSequenceModules.{u, u} l E W)
    {f g : (((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf.{u, u} l E W)).obj (P, Q)).X n) ⟶ H}
    (h : ∀ (p q : ℤ) (hpq : p + q = n) (V : (ℕ × W.ProEt)ᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      f.val.app V (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q n hpq V x y) =
      g.val.app V (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q n hpq V x y)) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply tensor_sections_ext l E W (P.X p) (Q.X q) H
  intro V x y
  exact h p q hpq V x y

private theorem generator_map
    {P P' Q Q' : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q n : ℤ) (hpq : p + q = n)
    (V : (ℕ × W.ProEt)ᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf.{u, u} l E W)).map (Prod.mkHom f g)).f n).val.app V
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q n hpq V x y) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W) P' Q' p q n hpq V
          ((f.f p).val.app V x) ((g.f q).val.app V y) := by
  have hi : HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n hpq ≫
      (((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W)).map (Prod.mkHom f g)).f n) =
      ((f.f p) ⊗ₘ (g.f q)) ≫
        HomologicalComplex.ιMapBifunctor P' Q' (curriedTensor _) (.up ℤ) p q n hpq := by
    change _ ≫ ((HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor _)
      (.up ℤ)).f n ≫ (HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor _)
        (.up ℤ)).f n) = _
    rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      whiskerLeft_id, Category.assoc]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      id_whiskerRight]
    rfl
  have hh := congrArg (fun a ↦ a.val.app V (tensorSection l E W (P.X p) (Q.X q) V x y)) hi
  change _ = (HomologicalComplex.ιMapBifunctor P' Q' (curriedTensor _) (.up ℤ)
    p q n hpq).val.app V
      (((f.f p) ⊗ₘ (g.f q)).val.app V (tensorSection l E W (P.X p) (Q.X q) V x y)) at hh
  rw [tensorSection_map] at hh
  exact hh

private theorem scalar_unit_section
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarUnit.{u, u} l E W).hom.app M).val.app V
      (integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W M V s x) =
        s • x := by
  exact (integralComparisonSequenceScalarUnit_existsUnique.{u, u} l E W).exists.choose_spec
    M V s x

private theorem scalar_unit_inv_section
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarUnit.{u, u} l E W).inv.app M).val.app V x =
      integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W M V 1 x := by
  have h := scalar_unit_section l E W M V 1 x
  have hh := congrArg
    (fun z ↦ ((integralComparisonSequenceScalarUnit.{u, u} l E W).inv.app M).val.app V z) h
  simpa only [one_smul, ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, Iso.hom_inv_id_app, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using hh.symm

/-- A scalar tensor comparison normalized on homogeneous unit tensors is compatible
with the scalar action unitor. Only the identity coefficient map is involved.
Source: Stacks 03EL and 07A4; scalar-extension tower coherence, proof step 7
(blueprint: lem-pur-scalar-tensor-unit).

Proof: precompose the asserted equality with the inverse scalar unitor of the
source tensor. Its value on a local homogeneous tensor x tensor y is the scalar
unit tensor 1 tensor (x tensor y). The assumed normalization sends it to
(1 tensor x) tensor (1 tensor y). Applying the two action unitors gives x tensor y.
The other route is the scalar unitor composed with its inverse, hence also fixes
x tensor y. Naturality of the sheafified tensor pairing commutes with both action
unitors. Pure tensors generate each presheaf tensor; the sheafification adjunction
extends equality to each tensor sheaf. The coproduct universal property extends it
to each total degree, and extensionality of chain maps and natural transformations
proves the claimed equality. Empty sites and zero complexes are included by these
same universal properties; no boundedness, flatness or invertibility of l is used. -/
theorem scalarExtensionTensorUnit
    (sigma : (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf.{u, u} l E W)) ⋙ ((integralComparisonSequenceScalarModel.{u,
        u}
      l E E (AlgHom.id ℚ_[l] E) W).E.mapHomologicalComplex (.up ℤ)) ≅
        (((integralComparisonSequenceScalarModel.{u, u}
      l E E (AlgHom.id ℚ_[l] E) W).E.mapHomologicalComplex (.up ℤ))).prod
        ((integralComparisonSequenceScalarModel.{u, u}
      l E E (AlgHom.id ℚ_[l] E) W).E.mapHomologicalComplex (.up ℤ)) ⋙ (coefficientTotalTensor.{u, u
        + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf.{u, u} l E W)))
    (h : ∀ (P Q : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
      (p q : ℤ) (V : (ℕ × W.ProEt)ᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      (((sigma.hom.app (P, Q)).f (p + q)).val.app V)
        (integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W
          ((((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf.{u, u} l E W))).obj (P, Q)).X (p + q)) V 1
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q (p + q) rfl V x y)) =
        coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l E W)
          ((((integralComparisonSequenceScalarModel.{u, u}
      l E E (AlgHom.id ℚ_[l] E) W).E.mapHomologicalComplex (.up ℤ))).obj P)
        ((((integralComparisonSequenceScalarModel.{u, u}
      l E E (AlgHom.id ℚ_[l] E) W).E.mapHomologicalComplex (.up ℤ))).obj Q) p q (p + q) rfl V
          (integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W
            (P.X p) V 1 x)
          (integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W
            (Q.X q) V 1 y)) :
    sigma ≪≫ Functor.isoWhiskerRight (NatIso.prod (NatIso.mapHomologicalComplex
      (integralComparisonSequenceScalarUnit.{u, u} l E W) (.up ℤ)) (NatIso.mapHomologicalComplex
      (integralComparisonSequenceScalarUnit.{u, u} l E W) (.up ℤ))) (coefficientTotalTensor.{u, u +
        1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf.{u, u} l E W)) =
      Functor.isoWhiskerLeft (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf.{u, u} l E W)) (NatIso.mapHomologicalComplex
      (integralComparisonSequenceScalarUnit.{u, u} l E W) (.up ℤ))  := by
  let T := coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W)
  let e := integralComparisonSequenceScalarUnit.{u, u} l E W
  let eC := NatIso.mapHomologicalComplex e (.up ℤ)
  apply Iso.ext
  apply NatTrans.ext
  funext PQ
  rcases PQ with ⟨P, Q⟩
  apply HomologicalComplex.hom_ext
  intro n
  change (sigma.hom.app (P, Q)).f n ≫
    (T.map (Prod.mkHom (eC.hom.app P) (eC.hom.app Q))).f n =
      e.hom.app ((T.obj (P, Q)).X n)
  -- Cancel the unitors before evaluating on sections.
  apply (cancel_epi (e.inv.app ((T.obj (P, Q)).X n))).1
  rw [Iso.inv_hom_id_app]
  apply total_tensor_sections_ext l E W P Q n
  intro p q hpq V x y
  subst n
  let z := coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q (p + q) rfl V x y
  let a := (T.map (Prod.mkHom (eC.hom.app P) (eC.hom.app Q))).f (p + q)
  let b := (sigma.hom.app (P, Q)).f (p + q)
  change a.val.app V (b.val.app V ((e.inv.app ((T.obj (P, Q)).X (p + q))).val.app V z)) = z
  -- Apply the section formulas directly, avoiding rewrite searches through the tensor model.
  refine (congrArg (fun t ↦ a.val.app V (b.val.app V t))
    (scalar_unit_inv_section l E W ((T.obj (P, Q)).X (p + q)) V z)).trans ?_
  refine (congrArg (fun t ↦ a.val.app V t) (h P Q p q V x y)).trans ?_
  refine (generator_map l E W (eC.hom.app P) (eC.hom.app Q) p q (p + q) rfl V
    (integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W
      (P.X p) V 1 x)
    (integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W
      (Q.X q) V 1 y)).trans ?_
  have hx := scalar_unit_section l E W (P.X p) V 1 x
  have hy := scalar_unit_section l E W (Q.X q) V 1 y
  simp only [one_smul] at hx hy
  exact congrArg₂ (fun a b ↦ coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q (p + q) rfl V a b) hx hy

end WeilConjectures
