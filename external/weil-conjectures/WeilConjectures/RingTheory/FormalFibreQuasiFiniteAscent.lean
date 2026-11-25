/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import WeilConjectures.RingTheory.CompletionAtQuasiFinitePrime
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Geometric regularity ascends along quasi-finite maps

Source: Stacks Project, More on Algebra, Lemma 07PP (blueprint:
lem-weil-pbc-formal-fibre-quasi-finite-ascent).
-/

@[expose] public section

universe u v

private theorem regularRing_fst
    (A B : Type*) [CommRing A] [CommRing B] [IsRegularRing (A × B)] :
    IsRegularRing A := by
  let M := Submonoid.powers ((1, 0) : A × B)
  apply RingTheory.isRegularRing_of_localization (A × B) A M (RingHom.fst A B)
  · intro s
    obtain ⟨n, hn⟩ := s.property
    change IsUnit s.val.1
    rw [← hn]
    simp
  · intro a
    refine ⟨(a, 0), 1, 1, isUnit_one, ?_, ?_⟩ <;> simp
  · intro r hr
    refine ⟨⟨(1, 0), Submonoid.mem_powers _⟩, ?_⟩
    apply Prod.ext <;> simp_all

namespace RingHom

/-- Geometric regularity of a formal fibre ascends along a map quasi-finite at the prime.
Source: Stacks Project, More on Algebra, Lemma 07PP, item (1)
(blueprint: lem-weil-pbc-formal-fibre-quasi-finite-ascent).
The fibre rings use Mathlib's residue-field-first tensor order, canonically isomorphic
as residue-field algebras to the completion-first order in the source.

Proof plan, following the six steps of the node:
1. Completion-at-quasi-finite-prime splits completion(R_p) ⊗[R] R' as
   completion(R'_(p')) × B, compatibly with the natural R'-algebra structures.
2. Tensor this splitting over R' with κ(q'); tensor products commute with finite
   products, so the target formal fibre F is a factor of the resulting algebra.
3. Since q is the contraction of q', localization-at-prime induces κ(q) → κ(q').
   Tensor-cancel-base-change, twice, identifies the resulting algebra with
   C = κ(q') ⊗[κ(q)] (κ(q) ⊗[R] completion(R_p)).
4. The images of finitely many R-algebra generators of R' generate κ(q') as a
   field extension of κ(q), so this extension is finitely generated.
5. For κ(q') itself or any finite purely inseparable extension L/κ(q'), L/κ(q)
   is finitely generated. Geometrically-regular-finitely-generated-extensions
   shows L ⊗[κ(q')] C is Noetherian and regular. Thus C is geometrically regular.
6. Tensor the splitting C ≅ F × B' with each such L. Projection to L ⊗[κ(q')] F
   is localization at the idempotent (1,0); localization-of-regular-ring makes
   this factor regular. Taking L = κ(q') gives Noetherianity of F. Thus F is
   geometrically regular over κ(q'), as required.
-/
theorem isRegular_formalFiber_of_isQuasiFiniteAtPrime
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing R']
    [Algebra R R'] [Algebra.FiniteType R R']
    (q' p' : Ideal R') [q'.IsPrime] [p'.IsPrime] (hqp : q' ≤ p')
    (hq : Algebra.IsQuasiFiniteAtPrime R R' ⟨p', inferInstance⟩)
    :
    let q := q'.comap (algebraMap R R')
    let p := p'.comap (algebraMap R R')
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)
    let C' := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
      (Localization.AtPrime p')
    Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) →
      Algebra.IsGeometricallyRegular q'.ResidueField (q'.Fiber C') := by
  classical
  dsimp only
  intro hA
  let q : Ideal R := q'.comap (algebraMap R R')
  let p : Ideal R := p'.comap (algebraMap R R')
  let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (Localization.AtPrime p)
  let C' := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
    (Localization.AtPrime p')
  have _hqpR : q ≤ p := Ideal.comap_mono hqp
  have : q.IsPrime := Ideal.comap_isPrime _ q'
  have : p.IsPrime := Ideal.comap_isPrime _ p'
  have : q'.LiesOver q := ⟨rfl⟩
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime q') :=
    Localization.AtPrime.algebraOfLiesOver q q'
  have : IsScalarTower R (Localization.AtPrime q) (Localization.AtPrime q') := inferInstance
  have hc := Algebra.completion_at_quasiFiniteAtPrime R R' ⟨p', inferInstance⟩ hq
  dsimp only [PrimeSpectrum.comap] at hc
  obtain ⟨ψ, _, B, hB, β, φ, hφ, e, he⟩ := hc
  let := hB
  let U := TensorProduct R C R'
  let : Algebra R' U := Algebra.TensorProduct.rightAlgebra
  let : Algebra R' B :=
    (β.comp (Algebra.TensorProduct.includeRight : R' →ₐ[R] U).toRingHom).toAlgebra
  have heval (y : R') : e (algebraMap R' U y) = algebraMap R' (C' × B) y := by
    have he' := DFunLike.congr_fun he (TensorProduct.tmul R (1 : C) y)
    apply Prod.ext
    · change (e (TensorProduct.tmul R (1 : C) y)).1 = algebraMap R' C' y
      refine (congrArg Prod.fst he').trans ?_
      change φ (TensorProduct.tmul R (1 : C) y) =
        algebraMap (Localization.AtPrime p') C' (algebraMap R' (Localization.AtPrime p') y)
      simpa only [map_one, one_mul] using hφ 1 y
    · change (e (TensorProduct.tmul R (1 : C) y)).2 = β (TensorProduct.tmul R 1 y)
      exact congrArg Prod.snd he'
  let eS : U ≃ₐ[R'] C' × B := { e with commutes' := heval }
  let ef : q'.Fiber U ≃ₐ[q'.ResidueField]
      TensorProduct q.ResidueField q'.ResidueField (q.Fiber C) :=
    (Algebra.TensorProduct.congr (.refl : q'.ResidueField ≃ₐ[q'.ResidueField]
      q'.ResidueField) (Algebra.TensorProduct.commRight R R' C).symm).trans
      ((Algebra.TensorProduct.cancelBaseChange R R' q'.ResidueField q'.ResidueField C).trans
        (Algebra.TensorProduct.cancelBaseChange R q.ResidueField
          q'.ResidueField q'.ResidueField C).symm)
  let eF : TensorProduct q.ResidueField q'.ResidueField (q.Fiber C) ≃ₐ[q'.ResidueField]
      q'.Fiber C' × (TensorProduct R' q'.ResidueField B) :=
    ef.symm.trans ((Algebra.TensorProduct.congr
      (.refl : q'.ResidueField ≃ₐ[q'.ResidueField] q'.ResidueField) eS).trans
      (Algebra.TensorProduct.prodRight R' q'.ResidueField q'.ResidueField C' B))
  have hfg := IntermediateField.fg_top q.ResidueField q'.ResidueField
  have : IsRegularRing (TensorProduct q.ResidueField q'.ResidueField (q.Fiber C)) :=
    Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular hA q'.ResidueField hfg
  have : IsRegularRing (q'.Fiber C' × (TensorProduct R' q'.ResidueField B)) :=
    IsRegularRing.of_ringEquiv eF.toRingEquiv
  have : IsRegularRing (q'.Fiber C') :=
    regularRing_fst (q'.Fiber C') (TensorProduct R' q'.ResidueField B)
  refine ⟨inferInstance, ?_⟩
  intro K _ _ _ _
  let : Algebra q.ResidueField K :=
    ((algebraMap q'.ResidueField K).comp (algebraMap q.ResidueField q'.ResidueField)).toAlgebra
  have : IsScalarTower q.ResidueField q'.ResidueField K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : Algebra.EssFiniteType q.ResidueField q'.ResidueField := inferInstance
  have : Algebra.EssFiniteType q.ResidueField K :=
    Algebra.EssFiniteType.comp q.ResidueField q'.ResidueField K
  have : IsRegularRing (TensorProduct q.ResidueField K (q.Fiber C)) :=
    Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular hA K
      (IntermediateField.fg_top q.ResidueField K)
  let eK := (Algebra.TensorProduct.cancelBaseChange q.ResidueField q'.ResidueField
    K K (q.Fiber C)).symm.trans
      ((Algebra.TensorProduct.congr (.refl : K ≃ₐ[K] K) eF).trans
        (Algebra.TensorProduct.prodRight q'.ResidueField K K (q'.Fiber C')
          (TensorProduct R' q'.ResidueField B)))
  have : IsRegularRing
      ((TensorProduct q'.ResidueField K (q'.Fiber C')) ×
        (TensorProduct q'.ResidueField K (TensorProduct R' q'.ResidueField B))) :=
    IsRegularRing.of_ringEquiv eK.toRingEquiv
  exact regularRing_fst (TensorProduct q'.ResidueField K (q'.Fiber C'))
    (TensorProduct q'.ResidueField K (TensorProduct R' q'.ResidueField B))

end RingHom
