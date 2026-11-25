/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Conormal stabilization by zero variables

Source: Stacks Project, Tag 07EZ, proof of part (e), stabilization paragraph
(blueprint: lem-weil-pbc-zero-variable-conormal-stabilization).
-/

@[expose] public section

universe u v
open scoped TensorProduct

namespace Algebra

open MvPolynomial _root_.TensorProduct

private noncomputable def zeroPresentation (A : Type v) [CommRing A] (r : ℕ) :
    SubmersivePresentation A A (Fin r) (Fin r) := by
  classical
  let G : Generators A A (Fin r) := .ofSurjective (fun _ => 0) (by
    intro x
    exact ⟨C x, by simp⟩)
  have hspan : Ideal.span (Set.range (X : Fin r → MvPolynomial (Fin r) A)) = G.ker := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro x ⟨i, rfl⟩
      simp [G, Generators.ker_eq_ker_aeval_val]
    · intro p hp
      have h (p : MvPolynomial (Fin r) A) :
          p - C (aeval (fun _ : Fin r => (0 : A)) p) ∈
            Ideal.span (Set.range (X : Fin r → MvPolynomial (Fin r) A)) := by
        induction p using MvPolynomial.induction_on with
        | C x => simp
        | add p q hp hq =>
          simpa only [map_add, add_sub_add_comm] using Ideal.add_mem _ hp hq
        | mul_X p i hp =>
          simpa using Ideal.mul_mem_left
            (Ideal.span (Set.range (X : Fin r → MvPolynomial (Fin r) A)))
            p (Ideal.subset_span ⟨i, rfl⟩)
      have hp' : aeval (fun _ : Fin r => (0 : A)) p = 0 := by
        change aeval G.val p = 0 at hp
        exact hp
      simpa [hp'] using h p
  let Q : PreSubmersivePresentation A A (Fin r) (Fin r) :=
    { toGenerators := G
      relation := X
      span_range_relation_eq_ker := hspan
      map := fun i => i
      map_inj := Function.injective_id }
  refine { toPreSubmersivePresentation := Q, jacobian_isUnit := ?_ }
  have hj : Q.jacobiMatrix = 1 := by
    ext i j : 1
    by_cases h : i = j <;>
      simp [PreSubmersivePresentation.jacobiMatrix_apply, Q, Matrix.one_apply,
        h, eq_comm]
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hj, Matrix.det_one,
    map_one]
  exact isUnit_one

private noncomputable def cotangentReindexEquiv
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {ι κ : Type} (G : Generators R A ι) (e : κ ≃ ι) :
    (G.reindex e).toExtension.Cotangent ≃ₗ[A] G.toExtension.Cotangent := by
  let f : (G.reindex e).Hom G :=
    { val := fun i => X (e i)
      aeval_val := fun i => by simp [Generators.reindex_val] }
  let g : G.Hom (G.reindex e) :=
    { val := fun i => X (e.symm i)
      aeval_val := fun i => by simp [Generators.reindex_val] }
  have hfg : f.comp g = Generators.Hom.id G := by
    ext i
    simp [f, g, Generators.Hom.comp, Generators.Hom.id]
  have hgf : g.comp f = Generators.Hom.id (G.reindex e) := by
    ext i
    simp [f, g, Generators.Hom.comp, Generators.Hom.id]
  refine LinearEquiv.ofLinearMap (Extension.Cotangent.map f.toExtensionHom)
    (Extension.Cotangent.map g.toExtensionHom) ?_ ?_
  · ext x
    change Extension.Cotangent.map f.toExtensionHom
      (Extension.Cotangent.map g.toExtensionHom x) = x
    have h := LinearMap.congr_fun
      (Extension.Cotangent.map_comp _ g.toExtensionHom f.toExtensionHom) x
    rw [← Generators.Hom.toExtensionHom_comp, hfg,
      Generators.Hom.toExtensionHom_id, Extension.Cotangent.map_id] at h
    exact h.symm
  · ext x
    change Extension.Cotangent.map g.toExtensionHom
      (Extension.Cotangent.map f.toExtensionHom x) = x
    have h := LinearMap.congr_fun
      (Extension.Cotangent.map_comp _ f.toExtensionHom g.toExtensionHom) x
    rw [← Generators.Hom.toExtensionHom_comp, hgf,
      Generators.Hom.toExtensionHom_id, Extension.Cotangent.map_id] at h
    exact h.symm

private noncomputable def zeroCompCotangentEquiv
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type} (G : Generators R A ι) (r : ℕ) :
    ((zeroPresentation A r).toGenerators.comp G).toExtension.Cotangent ≃ₗ[A]
      G.toExtension.Cotangent × (Fin r → A) := by
  classical
  let Q := zeroPresentation A r
  let W := Q.toGenerators.comp G
  let back : W.Hom G :=
    { val := Sum.elim (fun _ => 0) X
      aeval_val := by
        intro i
        cases i <;> simp [W, Q, zeroPresentation, Generators.comp] }
  have hback : back.comp (Q.toGenerators.toComp G) = Generators.Hom.id G := by
    ext i
    simp [back, Generators.Hom.comp, Generators.Hom.id, Generators.toComp]
  let f := (Extension.Cotangent.map (Q.toGenerators.toComp G).toExtensionHom).liftBaseChange A
  let l := (_root_.TensorProduct.lid A G.toExtension.Cotangent).symm.toLinearMap.comp
    (Extension.Cotangent.map back.toExtensionHom)
  have hl : l.comp f = LinearMap.id := by
    apply _root_.TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (_root_.TensorProduct.lid A G.toExtension.Cotangent).symm
      (Extension.Cotangent.map back.toExtensionHom
        (f (x ⊗ₜ[A] y))) = x ⊗ₜ[A] y
    rw [LinearMap.liftBaseChange_tmul, map_smul]
    have h := LinearMap.congr_fun
      (Extension.Cotangent.map_comp _
        (Q.toGenerators.toComp G).toExtensionHom back.toExtensionHom) y
    rw [← Generators.Hom.toExtensionHom_comp, hback,
      Generators.Hom.toExtensionHom_id, Extension.Cotangent.map_id] at h
    change y = Extension.Cotangent.map back.toExtensionHom
      (Extension.Cotangent.map (Q.toGenerators.toComp G).toExtensionHom y) at h
    rw [← h]
    simp [TensorProduct.smul_tmul']
  let e := ((Generators.Cotangent.exact Q.toGenerators G).splitInjectiveEquiv
    (Generators.Cotangent.surjective_map_ofComp Q.toGenerators G) ⟨l, hl⟩).1
  exact e.trans (LinearEquiv.prodCongr (_root_.TensorProduct.lid A G.toExtension.Cotangent)
    Q.cotangentEquiv)

/-- Adjoining exactly `r` variables sent to zero adds `r` free summands to the
localized conormal module. No freeness hypothesis on the old module is needed.

Source: Stacks Project, Tag 07EZ, proof of part (e), stabilization paragraph
(blueprint: lem-weil-pbc-zero-variable-conormal-stabilization).

Proof: construct the presentation Q of A over itself with r variables sent to zero
and relations X_i. Polynomial induction shows that the X_i generate its kernel.
Its Jacobian matrix is the identity, so Mathlib's submersive-presentation conormal
isomorphism identifies Cotangent(Q) with A^r. Compose Q with the old presentation.
Mathlib's conormal exact sequence for composed generators gives
A ⊗_A Cotangent(P₀) → Cotangent(Q.comp P₀) → Cotangent(Q) → 0.
Setting the new variables to zero gives a homomorphism back to P₀ whose composite
with the inclusion of the old variables is the identity. Functoriality of conormal
maps and the tensor unit isomorphism therefore give a retraction of the first map.
Split the exact sequence using this retraction and identify its two factors with
Cotangent(P₀) and A^r. Reindex variables and relations by Fin (n₀+r) and Fin (m₀+r);
the inverse renaming homomorphisms induce inverse conormal maps. Tensor the resulting
equivalence with A_a, distribute tensor over the product, and identify A_a ⊗_A A^r
with (A_a)^r. All steps allow r=0 and zero rings or zero localizations. Only
existential theorem data are produced. -/
theorem exists_zero_variable_presentation_localized_cotangent_equiv
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (a : A) {n₀ m₀ : ℕ} (P₀ : Presentation R A (Fin n₀) (Fin m₀)) (r : ℕ) :
    ∃ (P : Presentation R A (Fin (n₀ + r)) (Fin (m₀ + r))), Nonempty
      ((Localization.Away a ⊗[A] P.toExtension.Cotangent) ≃ₗ[Localization.Away a]
        ((Localization.Away a ⊗[A] P₀.toExtension.Cotangent) ×
          (Fin r → Localization.Away a))) := by
  classical
  let Q := zeroPresentation A r
  let Pc := Q.toPresentation.comp P₀
  let ev : Fin (n₀ + r) ≃ Fin r ⊕ Fin n₀ :=
    finSumFinEquiv.symm.trans (Equiv.sumComm _ _)
  let er : Fin (m₀ + r) ≃ Fin r ⊕ Fin m₀ :=
    finSumFinEquiv.symm.trans (Equiv.sumComm _ _)
  let P := Pc.reindex ev er
  let e := (cotangentReindexEquiv Pc.toGenerators ev).trans
    (zeroCompCotangentEquiv P₀.toGenerators r)
  let B := Localization.Away a
  refine ⟨P, ⟨?_⟩⟩
  exact (e.baseChange (A := B)).trans
    ((TensorProduct.prodRight A B B P₀.toExtension.Cotangent (Fin r → A)).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl B _)
        (TensorProduct.piScalarRight A B B (Fin r))))

end Algebra
