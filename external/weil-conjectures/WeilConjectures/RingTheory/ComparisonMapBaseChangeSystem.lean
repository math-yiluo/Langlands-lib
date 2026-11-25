/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import WeilConjectures.RingTheory.ComparisonTensorCocones
import WeilConjectures.RingTheory.DirectedTensorCoconesColimit

/-! # Extending a tensor comparison by base change

Source: Stacks Project, Algebra, Tags 02JO (3) and 00DD.
(blueprint: lem-weil-pbc-comparison-map-base-change-system)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

-- The ring equivalence in the hypothesis need not preserve the limit-ring scalars.
-- Splitting the coordinates of a countable product exhibits the obstruction.
private theorem comparison_scalar_obstruction :
    let A := ℕ → ℤ
    ∃ e : ((A ⊗[ℤ] ℤ) ⊗[ℤ] ℤ) ≃ₐ[ℤ] (A ⊗[ℤ] (ℤ × ℤ)),
      (∀ z : ℤ, e ((1 ⊗ₜ[ℤ] z) ⊗ₜ[ℤ] 1) = 1 ⊗ₜ[ℤ] (z, z)) ∧
      ¬Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id ℤ A)
          ((AlgHom.id ℤ ℤ).prod (AlgHom.id ℤ ℤ))) := by
  let A := ℕ → ℤ
  let split : A ≃ₐ[ℤ] A × A :=
    (AlgEquiv.piCongrLeft' ℤ (fun _ : ℕ ↦ ℤ) Equiv.natSumNatEquivNat.symm).trans
      (AlgEquiv.sumArrowEquivProdArrow ℕ ℕ ℤ ℤ)
  let rid : A ⊗[ℤ] ℤ ≃ₐ[ℤ] A := Algebra.TensorProduct.rid ℤ ℤ A
  let prod : A ⊗[ℤ] (ℤ × ℤ) ≃ₐ[ℤ] A × A :=
    (Algebra.TensorProduct.prodRight ℤ ℤ A ℤ ℤ).trans (rid.prodCongr rid)
  let e := ((Algebra.TensorProduct.rid ℤ ℤ (A ⊗[ℤ] ℤ)).trans rid).trans
    (split.trans prod.symm)
  refine ⟨e, ?_, ?_⟩
  · intro z
    apply prod.injective
    change prod (prod.symm (split (rid
      (Algebra.TensorProduct.rid ℤ ℤ (A ⊗[ℤ] ℤ) ((1 ⊗ₜ[ℤ] z) ⊗ₜ[ℤ] 1))))) = _
    rw [prod.apply_symm_apply]
    simp only [Algebra.TensorProduct.rid_tmul, one_smul]
    change split (z • (1 : A)) = _
    rw [← Algebra.algebraMap_eq_smul_one, split.commutes]
    simp [prod, rid, Algebra.TensorProduct.prodRight_tmul]
    rfl
  · intro hs
    obtain ⟨x, hx⟩ := hs (prod.symm (0, 1))
    have hdiag : ∀ x : A ⊗[ℤ] ℤ,
        prod (Algebra.TensorProduct.map (AlgHom.id ℤ A)
          ((AlgHom.id ℤ ℤ).prod (AlgHom.id ℤ ℤ)) x) = (rid x, rid x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a z => simp [prod, rid, Algebra.TensorProduct.prodRight_tmul]
      | add x y hx hy => simp [hx, hy]
    have heq := congrArg prod hx
    rw [hdiag, prod.apply_symm_apply] at heq
    have hz : (0 : A) = 1 := (congrArg Prod.fst heq).symm.trans (congrArg Prod.snd heq)
    exact zero_ne_one (congrFun hz 0)

-- A nonsurjective terminal component cannot induce a bijective map of colimits.
-- This rules out every choice of transitions in the version lacking scalar compatibility.
private theorem terminal_comparison_obstruction
    {J : Type v} [SmallCategory J] (D E : J ⥤ CommRingCat.{w}) (α : D ⟶ E)
    (t : J) (ht : IsTerminal t) (cD : Cocone D) (cE : Cocone E)
    (hD : IsColimit cD) (hE : IsColimit cE) (f : cD.pt ⟶ cE.pt)
    (hcomm : α.app t ≫ cE.ι.app t = cD.ι.app t ≫ f)
    (hnot : ¬Function.Surjective (α.app t)) : ¬Function.Bijective f := by
  intro hf
  let := hD.isIso_ι_app_of_isTerminal t ht
  let := hE.isIso_ι_app_of_isTerminal t ht
  have hDb := ConcreteCategory.bijective_of_isIso (cD.ι.app t)
  have hEb := ConcreteCategory.bijective_of_isIso (cE.ι.app t)
  apply hnot
  intro y
  obtain ⟨z, hz⟩ := hf.2 (cE.ι.app t y)
  obtain ⟨x, hx⟩ := hDb.2 z
  refine ⟨x, hEb.1 ?_⟩
  have h := ConcreteCategory.congr_hom hcomm x
  change cE.ι.app t (α.app t x) = f (cD.ι.app t x) at h
  simpa only [hx, hz] using h

-- At the terminal stage of Z -> (N -> Z), the last compatibility clause
-- alone contradicts the existence of the requested bijective colimit map.
private theorem comparison_terminal_tensor_obstruction
    {J : Type v} [SmallCategory J] (D E : J ⥤ CommRingCat.{0}) (α : D ⟶ E)
    (t : J) (ht : IsTerminal t) (cD : Cocone D) (cE : Cocone E)
    (hD : IsColimit cD) (hE : IsColimit cE) (f : cD.pt ⟶ cE.pt)
    (hcomm : α.app t ≫ cE.ι.app t = cD.ι.app t ≫ f)
    (d : D.obj t ≃+* (((ℕ → ℤ) ⊗[ℤ] ℤ) ⊗[ℤ] ℤ))
    (c : E.obj t ≃+* ((ℕ → ℤ) ⊗[ℤ] (ℤ × ℤ)))
    (hcompat :
      (c.toRingHom.comp ((α.app t).hom.comp d.symm.toRingHom)).comp
        (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
          (A := (ℕ → ℤ) ⊗[ℤ] ℤ) (B := ℤ)) =
        (Algebra.TensorProduct.map (AlgHom.id ℤ (ℕ → ℤ))
          ((AlgHom.id ℤ ℤ).prod (AlgHom.id ℤ ℤ))).toRingHom) :
    ¬Function.Bijective f := by
  apply terminal_comparison_obstruction D E α t ht cD cE hD hE f hcomm
  intro hα
  obtain ⟨_, _, hn⟩ := comparison_scalar_obstruction
  apply hn
  have hinc : Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
        (A := (ℕ → ℤ) ⊗[ℤ] ℤ) (B := ℤ)) := by
    intro x
    refine ⟨Algebra.TensorProduct.rid ℤ ℤ ((ℕ → ℤ) ⊗[ℤ] ℤ) x, ?_⟩
    exact (Algebra.TensorProduct.rid ℤ ℤ ((ℕ → ℤ) ⊗[ℤ] ℤ)).symm_apply_apply x
  have hs : Function.Surjective
      ((c.toRingHom.comp ((α.app t).hom.comp d.symm.toRingHom)).comp
        (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
          (A := (ℕ → ℤ) ⊗[ℤ] ℤ) (B := ℤ))) :=
    c.surjective.comp (hα.comp (d.symm.surjective.comp hinc))
  rw [hcompat] at hs
  exact hs


/-- Extend a single comparison map by base change to a pushout system with its colimits.

Source: Stacks Project, Algebra, Tag 02JO (3), the displayed maps Ψ and their
colimit; tensor universal properties and Tag 00DD.
(blueprint: lem-weil-pbc-comparison-map-base-change-system)

Proof: for j ≥ i, transport the P-structure of Bᵢ to Bⱼ by the tensor transition
map. Define Dⱼ as the common-universe ULift of Bⱼ tensor_P Q and Eⱼ as the ULift
of Cⱼ. Define their transitions by tensor maps. Tensor cancellation identifies
Bⱼ with F(j) tensor_{F(i)} Bᵢ and Cⱼ with F(j) tensor_{F(i)} Cᵢ.
Base change ψ along F(i) → F(j), and use these cancellation equivalences to
obtain αⱼ. The identity hψ makes ψ F(i)-linear, and also proves left-inclusion
compatibility after base change. Checking the B and Q inclusions proves
naturality. Explicitly, if qᵢ(q) = ψ(1 tensor q), the component on pure
tensors is b tensor q ↦ φⱼ(b) · τⱼᵢ(qᵢ(q)), where τ is the C transition.
The transported P-structure makes this balanced. For j → k, both source
and target at k are obtained from their
values at j by tensoring with Bₖ over Bⱼ; tensor associativity therefore proves
the transition square is a pushout. These identifications also define the
canonical d and c after the ULift conjugations.
The B and C tensor diagrams have their limit tensor rings as colimits, by the
elementwise representative and eventual-equality lemma. A compatible family
of maps from Dⱼ is exactly a compatible family of maps from Bⱼ and a map from
Q agreeing on P. Thus its colimit is B tensor_P Q. Construct cD and cE using
these universal properties and lift their points to the common universe.
Their comparison is the conjugate of e: he identifies its restriction to B,
and hlim identifies its restriction to Q by evaluation on 1 tensor q.
Tensor extensionality proves this identity at the limit. Consequently f
is bijective. This construction uses no finite-presentation assumptions and
works for arbitrary Q and φ₀, including zero rings.
-/
theorem exists_comparison_map_base_change_system
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (e : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (he : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      e.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom)
    (i : I) (hi : i₀ ≤ i)
    (aPi : letI := (F.map (homOfLE hi)).hom.toAlgebra
      Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀))
    (μB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      μB.toRingHom =
        (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom)
    (ψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ((↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q) →+* (↥(F.obj i) ⊗[F.obj i₀] C₀))
    (hψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ψ.comp (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom)
    (hlim : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp ψ =
        e.toRingHom.comp (Algebra.TensorProduct.map μB (AlgHom.id P Q)).toRingHom) :
      let J := {j : I // i ≤ j}
      ∃ (aPs : ∀ j : J,
          letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
        ∃ (D E : J ⥤ CommRingCat.{max v w x y}) (α : D ⟶ E),
          ∃ (d : ∀ j : J,
              letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
              letI := aPs j
              ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q),
            ∃ (c : ∀ j : J,
                letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀)),
              ∃ (cD : Cocone D) (cE : Cocone E) (f : cD.pt ⟶ cE.pt),
                ∃ (_hD : IsColimit cD) (_hE : IsColimit cE),
                (∀ j, α.app j ≫ cE.ι.app j = cD.ι.app j ≫ f) ∧
                Function.Bijective f ∧
                (∀ {j k} (r : j ⟶ k), IsPushout (α.app j) (D.map r)
                  (E.map r) (α.app k)) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                  letI := aPs j
                  ((c j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)).comp
                    (Algebra.TensorProduct.includeLeftRingHom (R := P)
                      (A := ↥(F.obj j.val) ⊗[F.obj i₀] B₀) (B := Q)) =
                    (Algebra.TensorProduct.map (Algebra.ofId (F.obj j.val) (F.obj j.val))
                      φ₀).toRingHom) := by
  classical
  obtain ⟨aPs, D, E, α, d, c, cD, cE, dLim, cLim, μs,
      hμs, hcD, hDt, hcE, hEt, hcomm, hpush, hcompat⟩ :=
    exists_comparison_tensor_cocones F i₀ B₀ C₀ φ₀ P Q aP e.toRingHom he
      i hi aPi μB hμB ψ hψ hlim
  obtain ⟨⟨hD⟩, ⟨hE⟩⟩ :=
    isColimit_directed_tensor_cocones F i₀ B₀ C₀ P Q aP i hi
      aPs D E d c cD cE dLim cLim μs hμs hcD hDt hcE hEt
  let _ := (colimit.ι F i₀).hom.toAlgebra
  let _ := aP
  let f : cD.pt ⟶ cE.pt :=
    CommRingCat.ofHom (cLim.symm.toRingHom.comp (e.toRingHom.comp dLim.toRingHom))
  refine ⟨aPs, D, E, α, d, c, cD, cE, f, hD, hE, ?_, ?_, hpush, hcompat⟩
  · intro j
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    apply cLim.injective
    have hz := DFunLike.congr_fun (hcomm j) z
    simpa [f] using hz
  · exact cLim.symm.bijective.comp (e.bijective.comp dLim.bijective)


end RingHom
