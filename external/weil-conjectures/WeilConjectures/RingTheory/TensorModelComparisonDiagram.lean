/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.RingTheory.ComparisonMapFiniteStage
import WeilConjectures.RingTheory.ComparisonTensorCocones
import WeilConjectures.RingTheory.DirectedTensorCoconesColimit
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.IsTensorProduct

/-! # A coherent tensor comparison diagram

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph; Tag 05N9.
(blueprint: lem-pc-tensor-model-comparison-diagram)
-/

@[expose] public section

universe v w x
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem finitePresentation_tensorMap {R B C T : Type*}
    [CommRing R] [CommRing B] [CommRing C] [CommRing T]
    [Algebra R B] [Algebra R C] [Algebra R T]
    (φ : B →ₐ[R] C) (hφ : φ.toRingHom.FinitePresentation) :
    (Algebra.TensorProduct.map (Algebra.ofId T T) φ).toRingHom.FinitePresentation := by
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FinitePresentation B C := hφ
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := T) (B := B)
  let e₁ := (Algebra.TensorProduct.comm B (T ⊗[R] B) C).toRingEquiv
  let e₂ := (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[B] C)
    (Algebra.TensorProduct.commRight R B T).symm).toRingEquiv
  let e₃ := (Algebra.TensorProduct.cancelBaseChange R B B C T).toRingEquiv
  let e₄ := (Algebra.TensorProduct.comm R C T).toRingEquiv
  let e := e₁.trans (e₂.trans (e₃.trans e₄))
  have hincl : (Algebra.TensorProduct.includeLeftRingHom (R := B)
      (A := T ⊗[R] B) (B := C)).FinitePresentation := by
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have he : (Algebra.TensorProduct.map (Algebra.ofId T T) φ).toRingHom =
      e.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := B)
        (A := T ⊗[R] B) (B := C)) := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext t
      simp [e, e₁, e₂, e₃, e₄, Algebra.smul_def]
    · ext b
      simp [e, e₁, e₂, e₃, e₄, Algebra.smul_def]
      rfl
  rw [he]
  exact (RingHom.FinitePresentation.of_bijective e.bijective).comp hincl


private theorem comparison_core
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    {i : I} {A B : Type w} [CommRing A] [CommRing B]
    [Algebra (F.obj i : Type v) A] [Algebra (F.obj i : Type v) B]
    [Algebra.FinitePresentation (F.obj i : Type v) A]
    [Algebra.FinitePresentation (F.obj i : Type v) B] (f : A →ₐ[F.obj i] B)
    (P Q : Type x) [CommRing P] [CommRing Q] [Algebra P Q]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    (aP : letI : Algebra (F.obj i : Type v) ↥(colimit F) := (colimit.ι F i).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i] A))
    (e : letI : Algebra (F.obj i : Type v) ↥(colimit F) := (colimit.ι F i).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i] A) ⊗[P] Q ≃+* ↥(colimit F) ⊗[F.obj i] B)
    (he : letI : Algebra (F.obj i : Type v) ↥(colimit F) := (colimit.ι F i).hom.toAlgebra
      letI := aP
      e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F))
          f).toRingHom) :
    ∃ (r : I) (hir : i ≤ r),
      let J := {j : I // r ≤ j}
      ∃ (aPs : ∀ j : J,
          letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
          Algebra P ((F.obj j.val : Type v) ⊗[F.obj i] A)),
        ∃ (D E : J ⥤ CommRingCat.{max v w x}) (α : D ⟶ E),
          ∃ (d : ∀ j : J,
              letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
              letI := aPs j
              (D.obj j : Type (max v w x)) ≃+*
                ((F.obj j.val : Type v) ⊗[F.obj i] A) ⊗[P] Q),
            ∃ (b : ∀ j : J,
                letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
                (E.obj j : Type (max v w x)) ≃+* (F.obj j.val : Type v) ⊗[F.obj i] B),
              ∃ (cD : Cocone D) (cE : Cocone E) (g : cD.pt ⟶ cE.pt),
                ∃ (_hD : IsColimit cD) (_hE : IsColimit cE), IsFiltered J ∧
                (∀ j, α.app j ≫ cE.ι.app j = cD.ι.app j ≫ g) ∧
                Function.Bijective g ∧
                (∀ j, (α.app j).hom.FinitePresentation) ∧
                (∀ {j k} (u : j ⟶ k), IsPushout (α.app j) (D.map u)
                  (E.map u) (α.app k)) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
                  letI := aPs j
                  let ψ := (b j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)
                  ψ.comp Algebra.TensorProduct.includeLeftRingHom =
                    (Algebra.TensorProduct.map (AlgHom.id (F.obj j.val) (F.obj j.val))
                      f).toRingHom) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
                  letI : Algebra (F.obj i : Type v) ↥(colimit F) :=
                    (colimit.ι F i).hom.toAlgebra
                  letI := aPs j
                  letI := aP
                  let t : F.obj j.val →ₐ[F.obj i] ↥(colimit F) :=
                    { (colimit.ι F j.val).hom with
                      commutes' := fun s ↦ ConcreteCategory.congr_hom
                        (colimit.w F (homOfLE (hir.trans j.property))) s }
                  let ψ := (b j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)
                  (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom.comp
                    (ψ.comp Algebra.TensorProduct.includeRight.toRingHom) =
                    e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
                  letI : Algebra (F.obj i : Type v) ↥(colimit F) :=
                    (colimit.ι F i).hom.toAlgebra
                  letI := aPs j
                  letI := aP
                  let t : F.obj j.val →ₐ[F.obj i] ↥(colimit F) :=
                    { (colimit.ι F j.val).hom with
                      commutes' := fun s ↦ ConcreteCategory.congr_hom
                        (colimit.w F (homOfLE (hir.trans j.property))) s }
                  (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) A)).toRingHom.comp
                    (algebraMap P ((F.obj j.val : Type v) ⊗[F.obj i] A)) =
                    algebraMap P (↥(colimit F) ⊗[F.obj i] A)) := by
  classical
  obtain ⟨r, hir, aPi, μB, hμB, ψ, hψ, hlim⟩ :=
    RingHom.exists_comparison_map_finite_stage F i A B f P Q aP e.toRingHom he
  obtain ⟨aPs, D, E, α, d, b, cD, cE, dLim, bLim, μs,
      hμs, hcD, hDt, hcE, hEt, hcomm, hpush, hcompat⟩ :=
    RingHom.exists_comparison_tensor_cocones F i A B f P Q aP e.toRingHom he
      r hir aPi μB hμB ψ hψ hlim
  obtain ⟨⟨hD⟩, ⟨hE⟩⟩ :=
    RingHom.isColimit_directed_tensor_cocones F i A B P Q aP r hir
      aPs D E d b cD cE dLim bLim μs hμs hcD hDt hcE hEt
  let := (colimit.ι F i).hom.toAlgebra
  let := aP
  let g : cD.pt ⟶ cE.pt :=
    CommRingCat.ofHom (bLim.symm.toRingHom.comp (e.toRingHom.comp dLim.toRingHom))
  have hfilt : IsFiltered {j : I // r ≤ j} := by
    have : Nonempty {j : I // r ≤ j} := ⟨⟨r, le_rfl⟩⟩
    have : IsDirected {j : I // r ≤ j} (· ≤ ·) := ⟨by
      intro j k
      obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
      exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
    infer_instance
  refine ⟨r, hir, aPs, D, E, α, d, b, cD, cE, g, hD, hE, hfilt, ?_,
    bLim.symm.bijective.comp (e.bijective.comp dLim.bijective), ?_, hpush, hcompat, ?_, ?_⟩
  · intro j
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    apply bLim.injective
    have hz := DFunLike.congr_fun (hcomm j) z
    simpa [g] using hz
  · intro j
    let := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
    let := aPs j
    let γ := (b j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)
    let inc := Algebra.TensorProduct.includeLeftRingHom (R := P)
      (A := (F.obj j.val : Type v) ⊗[F.obj i] A) (B := Q)
    have hinc : inc.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
    have hf : f.toRingHom.FinitePresentation := by
      let := f.toRingHom.toAlgebra
      let : IsScalarTower (F.obj i : Type v) A B :=
        .of_algebraMap_eq fun x ↦ (f.commutes x).symm
      exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation
        (R := (F.obj i : Type v)) (A := A) (B := B)
    have hγinc : (γ.comp inc).FinitePresentation := by
      rw [show γ.comp inc = _ from hcompat j]
      exact finitePresentation_tensorMap f hf
    have hγ : γ.FinitePresentation :=
      hγinc.of_comp_finiteType inc (RingHom.FiniteType.of_finitePresentation hinc)
    have hα := (RingHom.FinitePresentation.of_bijective (f := (b j).symm.toRingHom)
        (b j).symm.bijective).comp
      (hγ.comp (RingHom.FinitePresentation.of_bijective
        (f := (d j).toRingHom) (d j).bijective))
    convert hα using 1
    ext z
    simp [γ]
  · intro j
    let := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
    let := aPs j
    let t : F.obj j.val →ₐ[F.obj i] ↥(colimit F) :=
      { (colimit.ι F j.val).hom with
        commutes' := fun s ↦
          ConcreteCategory.congr_hom (colimit.w F (homOfLE (hir.trans j.property))) s }
    apply RingHom.ext
    intro q
    have he := DFunLike.congr_fun (hcE j) ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q)))
    have hcom := DFunLike.congr_fun (hcomm j) ((d j).symm (1 ⊗ₜ[P] q))
    have hd := DFunLike.congr_fun (hcD j) ((d j).symm (1 ⊗ₜ[P] q))
    simp only [RingHom.comp_apply] at he hcom hd
    have hd' : dLim ((cD.ι.app j).hom ((d j).symm (1 ⊗ₜ[P] q))) =
        1 ⊗ₜ[P] q := by simpa using hd
    change (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B))
      (b j ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q)))) = e (1 ⊗ₜ[P] q)
    exact he.symm.trans (hcom.trans (congrArg e hd'))
  · intro j
    let := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
    let := aPs j
    exact (congrArg (fun φ ↦ RingHom.comp φ (algebraMap P _)) (hμs j)).symm.trans
      (μs j).comp_algebraMap



/-- Construct the coherent comparison diagram, retaining its right-leg limit identity.

Source: Stacks Project, Algebra, Tag 02JO (3), construction of Ψ; Tags 00QO, 00DD,
and 05N9. (blueprint: lem-pc-tensor-model-comparison-diagram)

Proof: on the cofinal upper tail of i, tensoring F with A and B gives the
colimits X and Y, by stage representatives and eventual equality. Finite
presentation over the integers factors the P-structure of X through an A
stage. Above that stage use the induced P-structures on both tensor diagrams.
The map Q to Y given by the right inclusion followed by e is P-linear, since
he identifies the left inclusion. Finite presentation of Q over P factors
this map through a B stage. At every later j, extend the factor through the
transition and form ψj by the tensor universal property. Its left restriction
is id tensor f; its right restriction has the asserted image in Y.
Lift the stage rings to the common universe and conjugate their maps by the
ULift equivalences. Tensor associativity and cancellation identify every
transition square as a pushout. The two canonical cocones are colimits by
tensor universal properties; their comparison is conjugate to e by checking
both tensor inclusions, so it is bijective. Finally B is finitely presented
over A by finite-type cancellation, and base change gives this at every
stage. The source of ψj is finitely presented over the A stage by base change
of P to Q. Finite-type cancellation therefore makes ψj finitely presented.
Directed upper tails are nonempty, even for empty generator sets. These
arguments use neither injective transitions nor nonzero rings.
This statement only constructs comparison maps, not a stage inverse.
-/
theorem exists_tensor_model_comparison_diagram
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    (F : I ⥤ CommRingCat.{v}) (c : Cocone F) (hc : IsColimit c)
    {i : I} {A B : Type w} [CommRing A] [CommRing B]
    [Algebra (F.obj i : Type v) A] [Algebra (F.obj i : Type v) B]
    [Algebra.FinitePresentation (F.obj i : Type v) A]
    [Algebra.FinitePresentation (F.obj i : Type v) B] (f : A →ₐ[F.obj i] B)
    (P Q : Type x) [CommRing P] [CommRing Q] [Algebra P Q]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    (aP : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      Algebra P ((c.pt : Type v) ⊗[F.obj i] A))
    (e : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      ((c.pt : Type v) ⊗[F.obj i] A) ⊗[P] Q ≃+* (c.pt : Type v) ⊗[F.obj i] B)
    (he : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
        (Algebra.TensorProduct.map (Algebra.ofId (c.pt : Type v) (c.pt : Type v))
          f).toRingHom) :
    ∃ (r : I) (hir : i ≤ r),
      let J := {j : I // r ≤ j}
      ∃ (aPs : ∀ j : J,
          letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
          Algebra P ((F.obj j.val : Type v) ⊗[F.obj i] A)),
        ∃ (D E : J ⥤ CommRingCat.{max v w x}) (α : D ⟶ E),
          ∃ (d : ∀ j : J,
              letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
              letI := aPs j
              (D.obj j : Type (max v w x)) ≃+*
                ((F.obj j.val : Type v) ⊗[F.obj i] A) ⊗[P] Q),
            ∃ (b : ∀ j : J,
                letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
                (E.obj j : Type (max v w x)) ≃+* (F.obj j.val : Type v) ⊗[F.obj i] B),
              ∃ (cD : Cocone D) (cE : Cocone E) (g : cD.pt ⟶ cE.pt),
                ∃ (_hD : IsColimit cD) (_hE : IsColimit cE), IsFiltered J ∧
                (∀ j, α.app j ≫ cE.ι.app j = cD.ι.app j ≫ g) ∧
                Function.Bijective g ∧
                (∀ j, (α.app j).hom.FinitePresentation) ∧
                (∀ {j k} (u : j ⟶ k), IsPushout (α.app j) (D.map u)
                  (E.map u) (α.app k)) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
                  letI := aPs j
                  let ψ := (b j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)
                  ψ.comp Algebra.TensorProduct.includeLeftRingHom =
                    (Algebra.TensorProduct.map (AlgHom.id (F.obj j.val) (F.obj j.val))
                      f).toRingHom) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
                  letI : Algebra (F.obj i : Type v) (c.pt : Type v) :=
                    (c.ι.app i).hom.toAlgebra
                  letI := aPs j
                  letI := aP
                  let t : F.obj j.val →ₐ[F.obj i] c.pt :=
                    { (c.ι.app j.val).hom with
                      commutes' := fun s ↦ ConcreteCategory.congr_hom
                        (c.w (homOfLE (hir.trans j.property))) s }
                  let ψ := (b j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)
                  (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom.comp
                    (ψ.comp Algebra.TensorProduct.includeRight.toRingHom) =
                    e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
                  letI : Algebra (F.obj i : Type v) (c.pt : Type v) :=
                    (c.ι.app i).hom.toAlgebra
                  letI := aPs j
                  letI := aP
                  let t : F.obj j.val →ₐ[F.obj i] c.pt :=
                    { (c.ι.app j.val).hom with
                      commutes' := fun s ↦ ConcreteCategory.congr_hom
                        (c.w (homOfLE (hir.trans j.property))) s }
                  (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) A)).toRingHom.comp
                    (algebraMap P ((F.obj j.val : Type v) ⊗[F.obj i] A)) =
                    algebraMap P ((c.pt : Type v) ⊗[F.obj i] A)) := by
  classical
  let : HasColimit F := ⟨⟨⟨c, hc⟩⟩⟩
  let := (colimit.ι F i).hom.toAlgebra
  let : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
  let := aP
  let iso := colimit.isoColimitCocone (⟨c, hc⟩ : ColimitCocone F)
  let base : ↥(colimit F) ≃ₐ[F.obj i] c.pt :=
    { iso.commRingCatIsoToRingEquiv with
      commutes' := fun s ↦ ConcreteCategory.congr_hom
        (colimit.isoColimitCocone_ι_hom (⟨c, hc⟩ : ColimitCocone F) i) s }
  let XA := Algebra.TensorProduct.congr base (AlgEquiv.refl : A ≃ₐ[F.obj i] A)
  let XB := Algebra.TensorProduct.congr base (AlgEquiv.refl : B ≃ₐ[F.obj i] B)
  let aPc : Algebra P (↥(colimit F) ⊗[F.obj i] A) :=
    (XA.symm.toRingHom.comp (algebraMap P ((c.pt : Type v) ⊗[F.obj i] A))).toAlgebra
  let := aPc
  let XAP : (↥(colimit F) ⊗[F.obj i] A) ≃ₐ[P] ((c.pt : Type v) ⊗[F.obj i] A) :=
    { XA.toRingEquiv with commutes' := fun p ↦ XA.apply_symm_apply _ }
  let ec := (Algebra.TensorProduct.congr XAP (AlgEquiv.refl : Q ≃ₐ[P] Q)).toRingEquiv.trans
    (e.trans XB.symm.toRingEquiv)
  have hec : ec.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      (Algebra.TensorProduct.map (AlgHom.id ↥(colimit F) ↥(colimit F)) f).toRingHom := by
    apply RingHom.ext
    intro a
    apply XB.injective
    change XB (ec (a ⊗ₜ[P] 1)) = _
    have hex : XB (ec (a ⊗ₜ[P] 1)) = e (XA a ⊗ₜ[P] 1) := by
      simp [ec, XAP]
    rw [hex]
    rw [show e (XA a ⊗ₜ[P] 1) =
      Algebra.TensorProduct.map (AlgHom.id (c.pt : Type v) (c.pt : Type v)) f (XA a) from
      RingHom.congr_fun he (XA a)]
    clear hex
    induction a using TensorProduct.inductionOn with
    | tmul r a => simp [XA, XB]
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  obtain ⟨r, hir, aPs, D, E, α, d, b, cD, cE, g, hD, hE,
      hfilt, hcomm, hbij, hfp, hpush, hleft, hright, hcompat⟩ :=
    comparison_core F f P Q aPc ec hec
  refine ⟨r, hir, aPs, D, E, α, d, b, cD, cE, g, hD, hE,
    hfilt, hcomm, hbij, hfp, hpush, hleft, ?_, ?_⟩
  swap
  · intro j
    let := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
    let := aPs j
    let t : F.obj j.val →ₐ[F.obj i] c.pt :=
      { (c.ι.app j.val).hom with
        commutes' := fun s ↦ ConcreteCategory.congr_hom
          (c.w (homOfLE (hir.trans j.property))) s }
    let tc : F.obj j.val →ₐ[F.obj i] ↥(colimit F) :=
      { (colimit.ι F j.val).hom with
        commutes' := fun s ↦ ConcreteCategory.congr_hom
          (colimit.w F (homOfLE (hir.trans j.property))) s }
    have hmapA : XA.toRingHom.comp
        (Algebra.TensorProduct.map tc (AlgHom.id (F.obj i) A)).toRingHom =
        (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) A)).toRingHom := by
      apply RingHom.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
      | tmul s a =>
        change base (tc s) ⊗ₜ[F.obj i] a = t s ⊗ₜ[F.obj i] a
        congr 1
        exact ConcreteCategory.congr_hom
          (colimit.isoColimitCocone_ι_hom (⟨c, hc⟩ : ColimitCocone F) j.val) s
    change (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) A)).toRingHom.comp
        (algebraMap P ((F.obj j.val : Type v) ⊗[F.obj i] A)) =
      algebraMap P ((c.pt : Type v) ⊗[F.obj i] A)
    rw [← hmapA, RingHom.comp_assoc]
    refine (congrArg (fun φ ↦ XA.toRingHom.comp φ) (hcompat j)).trans ?_
    apply RingHom.ext
    intro p
    exact XA.apply_symm_apply _
  intro j
  let := (F.map (homOfLE (hir.trans j.property))).hom.toAlgebra
  let := aPs j
  let t : F.obj j.val →ₐ[F.obj i] c.pt :=
    { (c.ι.app j.val).hom with
      commutes' := fun s ↦ ConcreteCategory.congr_hom
        (c.w (homOfLE (hir.trans j.property))) s }
  let tc : F.obj j.val →ₐ[F.obj i] ↥(colimit F) :=
    { (colimit.ι F j.val).hom with
      commutes' := fun s ↦ ConcreteCategory.congr_hom
        (colimit.w F (homOfLE (hir.trans j.property))) s }
  have hmap : XB.toRingHom.comp
      (Algebra.TensorProduct.map tc (AlgHom.id (F.obj i) B)).toRingHom =
      (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
    | tmul s b =>
      change base (tc s) ⊗ₜ[F.obj i] b = t s ⊗ₜ[F.obj i] b
      congr 1
      exact ConcreteCategory.congr_hom
        (colimit.isoColimitCocone_ι_hom (⟨c, hc⟩ : ColimitCocone F) j.val) s
  apply RingHom.ext
  intro q
  have hq := RingHom.congr_fun (hright j) q
  have ht := RingHom.congr_fun hmap
    ((b j).toRingHom ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q))))
  change (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B))
    (b j ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q)))) = e (1 ⊗ₜ[P] q)
  change XB ((Algebra.TensorProduct.map tc (AlgHom.id (F.obj i) B))
      (b j ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q))))) =
    (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B))
      (b j ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q)))) at ht
  have hq' : (Algebra.TensorProduct.map tc (AlgHom.id (F.obj i) B))
      (b j ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q)))) = ec (1 ⊗ₜ[P] q) := hq
  refine ht.symm.trans ((congrArg XB hq').trans ?_)
  simp [ec, XAP]

end AlgebraicGeometry
