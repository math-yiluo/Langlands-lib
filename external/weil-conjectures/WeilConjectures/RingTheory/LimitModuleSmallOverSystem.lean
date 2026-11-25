/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.RingTheory.LimitModuleEssentiallyFinitePresentationOverSystem
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Small-universe module descent over an essentially finite type base system
Source: Stacks Project, Algebra, Tags 00QV, 00QX and 00R1.
(blueprint: lem-weil-pbc-limit-module-small-over-system)
-/

@[expose] public section

universe u v p

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

private theorem countable_of_essFiniteType (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Countable R] [Algebra.EssFiniteType R S] : Countable S := by
  classical
  let S₀ := Algebra.EssFiniteType.subalgebra R S
  let W := Algebra.EssFiniteType.submonoid R S
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := S₀)).mp
    inferInstance
  have : Countable (MvPolynomial (Fin n) R) := by
    exact (AddMonoidAlgebra.coeff_injective (R := R) (M := Fin n →₀ ℕ)).countable
  have : Countable S₀ := hf.countable
  exact (IsLocalization.mk'_surjective W (S := S)).countable

/-- Single-ring descent with the module diagram in the universe of the limit module.
The extra essential finite type hypothesis permits shrinking the finite stage modules.

Source: Stacks Project, Algebra, Tags 00QV, 00QX and 00R1, with the universe transport
in the proof of `lem-weil-pbc-limit-tower-over-local-system`.
(blueprint: lem-weil-pbc-limit-module-small-over-system)

Proof: Lift N to ULift in universe max u v, carrying its additive group and T-module
structure along ULift.down. Compose the given cokernel equivalence with the inverse
linear equivalence of this lift. Apply
`exists_limit_module_essentially_finite_presentation_over_system` to the lifted module.
Keep its tail, stage rings, ring maps, localness, colimit and ring tensor comparisons.
Each stage ring is essentially of finite type over Z: compose the supplied base
essential finite type map with the descended structure map. An essentially finite
type algebra over a countable ring is countable: its finite set of essential generators
spans a countable polynomial quotient, and its localization consists of fractions
represented by pairs in that countable quotient. Each descended stage module is a
quotient of a finite power of this countable ring by its descended matrix range,
so it is countable and hence small in universe v.
Choose Shrink in universe v for each of these concrete stage modules, transporting
its additive group and module structure through equivShrink. Define each transition
by conjugating the original transition with the two equivalences. Define the cocone
components by the same conjugation at the source and ULift.down at the target.
The inverse equivalences show the identity and composition laws and naturality.
Transport the cokernel and tensor equivalences by these module equivalences;
semilinearity gives the induced tensor equivalences, and checking pure tensors
proves the displayed formulas. For the colimit universal property, lift a test cocone
in universe v to universe max u v, use the original IsColimit, and conjugate its
descending map back; the component equalities and uniqueness follow by the inverse
bijections. These operations preserve all returned clauses, including the component
identifications for the auxiliary maps. Empty Fin s or Fin t are included: their
finite powers and quotients are still countable, and no nonzero-rank assumption is used.
-/
theorem exists_limit_module_small_over_system
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hFfinite : ∀ i, Algebra.EssFiniteType ℤ (F.obj i))
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (P : Type p) [CommRing P] [Algebra c.pt P] [Algebra.FinitePresentation c.pt P]
    (W : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap c.pt P) = τ)
    (hT : letI := f.toAlgebra; IsLocalization W T)
    (N : AddCommGrpCat.{v}) [Module T N]
    (s t : ℕ) (H : (Fin s → T) →ₗ[T] (Fin t → T))
    (hN : Nonempty (((Fin t → T) ⧸ LinearMap.range H) ≃ₗ[T] N)) :
    ∃ i₀ : I,
      ∃ (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u}) (β : B ⟶ (Functor.const _).obj T),
        Nonempty (IsColimit (Cocone.mk T β)) ∧
        ∃ (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T),
          (∀ i, ∀ x : B.obj i, κ i x = (β.app i).hom x) ∧
          (∀ i, IsLocalRing (B.obj i)) ∧ (∀ i, IsLocalHom (κ i)) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            IsLocalHom (B.map (homOfLE h)).hom) ∧
          ∃ (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i),
            (∀ i, IsLocalHom (τ₀ i)) ∧ (∀ i, (τ₀ i).EssFiniteType) ∧
            (∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom) ∧
            (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
              (B.map (homOfLE h)).hom.comp (τ₀ i) =
                (τ₀ j).comp (F.map (homOfLE h)).hom) ∧
            ∃ (D : {i : I // i₀ ≤ i} ⥤ AddCommGrpCat.{v})
              (δ : D ⟶ (Functor.const _).obj N),
              Nonempty (IsColimit (Cocone.mk N δ)) ∧
              ∃ (ν : ∀ i : {i : I // i₀ ≤ i}, D.obj i →+ N)
                (_ : ∀ i : {i : I // i₀ ≤ i}, Module (B.obj i) (D.obj i)),
                (∀ i, ∀ x : D.obj i, ν i x = (δ.app i).hom x) ∧
                (∀ i, ∀ (y : B.obj i) (x : D.obj i), ν i (y • x) = κ i y • ν i x) ∧
                (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j)
                  (y : B.obj i) (x : D.obj i),
                  (D.map (homOfLE h)).hom (y • x) =
                    (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
                (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
                (∀ i, ∃ H₀ : (Fin s → B.obj i) →ₗ[B.obj i] (Fin t → B.obj i),
                  Nonempty (((Fin t → B.obj i) ⧸ LinearMap.range H₀) ≃ₗ[B.obj i] D.obj i)) ∧
                (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
                  letI := (τ₀ i).toAlgebra
                  letI := (F.map (homOfLE h)).hom.toAlgebra
                  (∃ φ : B.obj i ⊗[F.obj i.1] F.obj j.1 →+* B.obj j,
                    (∀ (x : B.obj i) (y : F.obj j.1),
                      φ (x ⊗ₜ[F.obj i.1] y) =
                        (B.map (homOfLE h)).hom x * τ₀ j y) ∧
                    (letI := φ.toAlgebra
                     ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] F.obj j.1),
                       IsLocalization U (B.obj j))) ∧
                  (letI := (B.map (homOfLE h)).hom.toAlgebra
                   ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
                     ∀ (y : B.obj j) (x : D.obj i),
                       e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x)) ∧
                (∀ i : {i : I // i₀ ≤ i},
                  letI := (τ₀ i).toAlgebra
                  letI : Algebra (F.obj i.1) c.pt := (c.ι.app i.1).hom.toAlgebra
                  (∃ φ : B.obj i ⊗[F.obj i.1] c.pt →+* T,
                    (∀ (x : B.obj i) (y : c.pt),
                      φ (x ⊗ₜ[F.obj i.1] y) = κ i x * τ y) ∧
                    (letI := φ.toAlgebra
                     ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] c.pt), IsLocalization U T)) ∧
                  (letI := (κ i).toAlgebra
                   ∃ e : T ⊗[B.obj i] D.obj i ≃ₗ[T] N,
                     ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B.obj i] x) = y • ν i x)) := by
  classical
  let N' : AddCommGrpCat.{max u v} := AddCommGrpCat.of (ULift.{u} N)
  let eN : N' ≃ₗ[T] N := ULift.moduleEquiv
  obtain ⟨i₀, B, β, hBcol, κ, hκ, hBlocal, hκlocal, hBmap, τ₀, hτlocal,
      hτfinite, hτcomp, hτnat, D, δ, hDcol, ν, hModule, hν, hνsmul, hmap,
      hfinite, hpres, htrans, hlimit⟩ :=
    exists_limit_module_essentially_finite_presentation_over_system F c hc hF hcLocal
      T τ P W f hf hT N' s t H ⟨hN.some.trans eN.symm⟩
  have hBcount (i : {i : I // i₀ ≤ i}) : Countable (B.obj i) := by
    let : Algebra (F.obj i.1) (B.obj i) := (τ₀ i).toAlgebra
    have : Algebra.EssFiniteType (F.obj i.1) (B.obj i) := hτfinite i
    have : Algebra.EssFiniteType ℤ (F.obj i.1) := hFfinite i.1
    have : Algebra.EssFiniteType ℤ (B.obj i) :=
      Algebra.EssFiniteType.comp ℤ (F.obj i.1) (B.obj i)
    exact countable_of_essFiniteType ℤ (B.obj i)
  have hDcount (i : {i : I // i₀ ≤ i}) : Countable (D.obj i) := by
    have := hBcount i
    obtain ⟨H₀, ⟨e⟩⟩ := hpres i
    have : Countable ((Fin t → B.obj i) ⧸ LinearMap.range H₀) :=
      H₀.range.mkQ_surjective.countable
    exact Countable.of_equiv _ e.toEquiv
  let E : {i : I // i₀ ≤ i} ⥤ AddCommGrpCat.{v} :=
    { obj := fun i ↦ AddCommGrpCat.of (Shrink.{v} (D.obj i))
      map := fun {i j} g ↦ AddCommGrpCat.ofHom
        (((Shrink.addEquiv.{v} (α := D.obj j)).symm.toAddMonoidHom.comp (D.map g).hom).comp
          (Shrink.addEquiv.{v} (α := D.obj i)).toAddMonoidHom)
      map_id := by intro i; ext x; simp
      map_comp := by intro i j k g h; ext x; simp }
  let e (i : {i : I // i₀ ≤ i}) : E.obj i ≃ₗ[B.obj i] D.obj i :=
    Shrink.linearEquiv.{v} (B.obj i) (D.obj i)
  let ε : E ⟶ (Functor.const _).obj N :=
    { app := fun i ↦ AddCommGrpCat.ofHom
        ((eN.toAddMonoidHom.comp (δ.app i).hom).comp (e i).toAddMonoidHom)
      naturality := by
        intro i j g
        ext x
        dsimp [E, e]
        simp only [Shrink.linearEquiv, Shrink.addEquiv, AddEquiv.linearEquiv_apply,
          Equiv.addEquiv_apply, Equiv.addEquiv_symm_apply, Equiv.apply_symm_apply]
        change eN ((δ.app j).hom ((D.map g).hom ((e i) x))) =
          eN ((δ.app i).hom ((e i) x))
        exact congrArg eN (congrArg (fun k ↦ k.hom ((e i) x)) (δ.naturality g)) }
  let ν' (i : {i : I // i₀ ≤ i}) : E.obj i →+ N := (ε.app i).hom
  have hEcol : Nonempty (IsColimit (Cocone.mk N ε)) := by
    let α : E ⋙ AddCommGrpCat.uliftFunctor.{u, v} ≅ D :=
      NatIso.ofComponents
        (fun i ↦ (AddEquiv.ulift.trans (e i).toAddEquiv).toAddCommGrpIso)
        (by
          intro i j g
          ext x
          dsimp [E, e]
          change (equivShrink.{v} (D.obj j)).symm
            ((equivShrink.{v} (D.obj j)) ((D.map g).hom
              ((equivShrink.{v} (D.obj i)).symm x.down))) =
            (D.map g).hom ((equivShrink.{v} (D.obj i)).symm x.down)
          exact Equiv.symm_apply_apply _ _)
    have hcol := (IsColimit.precomposeHomEquiv α (Cocone.mk N' δ)).symm hDcol.some
    apply Nonempty.intro
    apply isColimitOfReflects AddCommGrpCat.uliftFunctor.{u, v}
    apply IsColimit.ofIsoColimit hcol
    refine Cocone.ext (Iso.refl _) ?_
    intro i
    ext x
    dsimp [α, ε, e, eN, N']
    change (δ.app i).hom ((equivShrink.{v} (D.obj i)).symm x.down) =
      ULift.up (((δ.app i).hom ((equivShrink.{v} (D.obj i)).symm x.down)).down)
    rfl
  refine ⟨i₀, B, β, hBcol, κ, hκ, hBlocal, hκlocal, hBmap, τ₀, hτlocal,
    hτfinite, hτcomp, hτnat, E, ε, hEcol, ν', (fun i ↦ inferInstance), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    rfl
  · intro i y x
    change eN ((δ.app i).hom ((e i) (y • x))) =
      κ i y • eN ((δ.app i).hom ((e i) x))
    rw [← hν, ← hν, (e i).map_smul, hνsmul]
    exact eN.map_smul _ _
  · intro i j h y x
    apply (e j).injective
    dsimp [E, e]
    simp only [Shrink.linearEquiv, Shrink.addEquiv, AddEquiv.linearEquiv_apply,
      Equiv.addEquiv_apply, Equiv.addEquiv_symm_apply, Equiv.apply_symm_apply,
      equivShrink_symm_smul]
    exact hmap i j h y _
  · intro i
    have := hfinite i
    exact Module.Finite.of_surjective (e i).symm.toLinearMap (e i).symm.surjective
  · intro i
    obtain ⟨H₀, ⟨e₀⟩⟩ := hpres i
    exact ⟨H₀, ⟨e₀.trans (e i).symm⟩⟩
  · intro i j h
    refine ⟨(htrans i j h).1, ?_⟩
    let : Algebra (B.obj i) (B.obj j) := (B.map (homOfLE h)).hom.toAlgebra
    obtain ⟨e₀, he₀⟩ := (htrans i j h).2
    refine ⟨((e i).baseChange (B.obj i) (B.obj j)).trans (e₀.trans (e j).symm), ?_⟩
    intro y x
    apply (e j).injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
      LinearEquiv.apply_symm_apply, he₀, map_smul]
    dsimp [E, e]
    simp [Shrink.linearEquiv, Shrink.addEquiv]
  · intro i
    refine ⟨(hlimit i).1, ?_⟩
    let : Algebra (B.obj i) T := (κ i).toAlgebra
    obtain ⟨e₀, he₀⟩ := (hlimit i).2
    refine ⟨((e i).baseChange (B.obj i) T).trans (e₀.trans eN), ?_⟩
    intro y x
    simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, he₀, map_smul]
    change y • eN (ν i ((e i) x)) = y • eN ((δ.app i).hom ((e i) x))
    rw [hν]

end RingHom
