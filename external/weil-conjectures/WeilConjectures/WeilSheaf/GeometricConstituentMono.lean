/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricConstituent

/-!
# Geometric constituents of an irreducible Weil sheaf are subsheaves

Let `X̄` be irreducible and `F` an irreducible lisse Weil sheaf on `X`. Every irreducible lisse
subquotient `A` of the underlying sheaf `F̄` on `X̄` is isomorphic to a lisse subsheaf of `F̄`:
`F̄` is a quotient of a finite sum `S_0 ⊕ ⋯ ⊕ S_N` of Frobenius translates of an irreducible
subsheaf `S_0 ⊆ F̄`, each of which is a subsheaf of `F̄`, and a nonzero morphism from some `S_k`
to `A` is an isomorphism by irreducibility. This is the semisimplicity half of the
sheaf-theoretic Clifford theorem, as in
`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_iso_biproduct_unit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Fact (ringChar k₀ ≠ l)]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

/-- An irreducible lisse Weil sheaf `F` with `X̄` irreducible: the underlying sheaf `F̄` is a
quotient of a finite sum `S_0 ⊕ ⋯ ⊕ S_{N-1}` of irreducible lisse subsheaves `S_i ⊆ F̄`
(the Frobenius translates of an irreducible subsheaf of `F̄`). -/
theorem IsIrreducibleLisse.exists_epi_biproduct_desc {F : WeilSheaf k₀ l X}
    (hF : F.IsIrreducibleLisse) :
    ∃ (N : ℕ) (S : Fin N → AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (m : ∀ i, S i ⟶ F.obj.carrier), (∀ i, IsIrreducibleAdicLocalSystem (S i)) ∧
      (∀ i, Mono (m i)) ∧ Epi (biproduct.desc m) := by
  classical
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let E := frobeniusPullback k₀ l X
  let φ := F.obj.str
  have hFl : IsAdicLisseSheaf F.obj.carrier := hF.1
  have hF0 : ¬ IsZero F.obj.carrier := fun h ↦ hF.2.1 (isZero_iff_isZero_carrier.2 h)
  obtain ⟨S₀, j₀, hj₀, hS₀⟩ := hFl.exists_mono_isIrreducibleAdicLocalSystem hF0
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y
  let d (A : AdicSheaf l Y) : ℕ := Module.finrank (PadicAlgCl l)
    ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj A))
  -- the Frobenius translates `S_n` of `S₀`, with their embeddings `m_n : S_n ⟶ F̄`
  let seq : ℕ → Σ A : AdicSheaf l Y, A ⟶ F.obj.carrier := fun n ↦
    Nat.rec ⟨S₀, j₀⟩ (fun _ q ↦ ⟨E.obj q.1, E.map q.2 ≫ φ.hom⟩) n
  have hmono (n : ℕ) : Mono (seq n).2 := by
    induction n with
    | zero => exact hj₀
    | succ n ih =>
      change Mono (E.map (seq n).2 ≫ φ.hom)
      infer_instance
  have hirr (n : ℕ) : IsIrreducibleAdicLocalSystem (seq n).1 := by
    induction n with
    | zero => exact hS₀
    | succ n ih => exact isIrreducibleAdicLocalSystem_frobeniusPullback_obj ih
  -- the sums `S_0 + ⋯ + S_{N-1}`, images of `σ_N : S_0 ⊕ ⋯ ⊕ S_{N-1} ⟶ F̄`
  let σ (N : ℕ) : (⨁ fun i : Fin N ↦ (seq i).1) ⟶ F.obj.carrier :=
    biproduct.desc fun i ↦ (seq i).2
  have hW (N : ℕ) : IsAdicLisseSheaf (⨁ fun i : Fin N ↦ (seq i).1) :=
    IsAdicLisseSheaf.biproduct_fin N _ fun i ↦ (hirr i).1
  have hT (N : ℕ) : IsAdicLisseSheaf (image (σ N)) := (hW N).image hFl (σ N)
  let incl (N : ℕ) :
      (⨁ fun i : Fin N ↦ (seq i).1) ⟶ ⨁ fun i : Fin (N + 1) ↦ (seq i).1 :=
    biproduct.desc fun i ↦ biproduct.ι (fun i : Fin (N + 1) ↦ (seq i).1) i.castSucc
  have hσ (N : ℕ) : incl N ≫ σ (N + 1) = σ N := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    simp [σ, incl]
  have hmon (N : ℕ) : d (image (σ N)) ≤ d (image (σ (N + 1))) := by
    have : Mono (image.eqToHom (hσ N).symm ≫ image.preComp (incl N) (σ (N + 1))) := by
      infer_instance
    exact finrank_geometricStalkFunctor_le_of_mono (hT _)
      (image.eqToHom (hσ N).symm ≫ image.preComp (incl N) (σ (N + 1))) s
  have hbd (N : ℕ) : d (image (σ N)) ≤ d F.obj.carrier :=
    finrank_geometricStalkFunctor_le_of_mono hFl (image.ι (σ N)) s
  -- the sums stabilise
  obtain ⟨N, hN⟩ : ∃ N, d (image (σ (N + 1))) ≤ d (image (σ N)) := by
    by_contra! h
    have key (N : ℕ) : N ≤ d (image (σ N)) := by
      induction N with
      | zero => exact Nat.zero_le _
      | succ N ih => exact ih.trans_lt (h N)
    exact absurd (key _) (Nat.not_le.2 (Nat.lt_succ_of_le (hbd (d F.obj.carrier + 1))))
  let c := image.eqToHom (hσ N).symm ≫ image.preComp (incl N) (σ (N + 1))
  have hc : c ≫ image.ι (σ (N + 1)) = image.ι (σ N) := by
    simp only [c, Category.assoc, image.preComp_ι]
    exact image.lift_fac _
  have : IsIso c := (hT N).isIso_of_mono_of_finrank_eq (hT (N + 1)) c s (le_antisymm (hmon N) hN)
  let T := image (σ N)
  let ι : T ⟶ F.obj.carrier := image.ι (σ N)
  -- `S_0, …, S_N` lie in `T`
  have hfac (k : ℕ) (hk : k ≤ N) : (seq k).2 ≫ cokernel.π ι = 0 := by
    have h1 : (seq k).2 = biproduct.ι (fun i : Fin (N + 1) ↦ (seq i).1) ⟨k, by omega⟩ ≫
        factorThruImage (σ (N + 1)) ≫ inv c ≫ ι := by
      rw [(IsIso.inv_comp_eq c).2 hc.symm, image.fac]
      simp [σ]
    rw [h1]
    simp [ι]
  -- `T` is carried into itself by `φ ∘ Fr^*`
  have hkey : E.map ι ≫ φ.hom ≫ cokernel.π ι = 0 := by
    rw [← cancel_epi (E.map (factorThruImage (σ N))), comp_zero, ← Functor.map_comp_assoc,
      image.fac, ← cancel_epi (E.mapBiproduct _).inv, comp_zero, Functor.mapBiproduct_inv]
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    simp only [biproduct.ι_desc_assoc, comp_zero, ← Functor.map_comp_assoc, σ,
      biproduct.ι_desc]
    exact hfac (i + 1) (by omega)
  -- hence onto itself, by rank, and `T` underlies a Weil subsheaf of `F`
  let u : E.obj T ⟶ T := Abelian.monoLift ι (E.map ι ≫ φ.hom) hkey
  have hu : u ≫ ι = E.map ι ≫ φ.hom := Abelian.monoLift_comp _ _ _
  have : Mono u := by
    have : Mono (u ≫ ι) := by rw [hu]; infer_instance
    exact mono_of_mono u ι
  have : IsIso u := (isAdicLisseSheaf_frobeniusPullback_obj (hT N)).isIso_of_mono_of_finrank_eq
    (hT N) u s (finrank_geometricStalkFunctor_frobeniusPullback_obj (hT N) s)
  let G : WeilSheaf k₀ l X :=
    ⟨Endofunctor.IsoAlgebra.mk T (asIso u), (hT N).isAdicConstructibleSheaf⟩
  let g : G ⟶ F := ObjectProperty.homMk (ObjectProperty.homMk ⟨ι, hu.symm⟩)
  have : Mono g := by
    have : Mono ((ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).map g) :=
      inferInstanceAs (Mono ι)
    exact (ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).mono_of_mono_map this
  have hιiso : IsIso ι := by
    rcases hF.2.2 G g inferInstance (hT N) with hz | hiso
    · have hz' : IsZero T := isZero_iff_isZero_carrier.1 hz
      have : Mono (Abelian.monoLift ι (seq 0).2 (hfac 0 (Nat.zero_le _))) := by
        have : Mono (Abelian.monoLift ι (seq 0).2 (hfac 0 (Nat.zero_le _)) ≫ ι) := by
          rw [Abelian.monoLift_comp]
          exact hmono 0
        exact mono_of_mono _ ι
      exact (hS₀.2.1 (IsZero.of_mono
        (Abelian.monoLift ι (seq 0).2 (hfac 0 (Nat.zero_le _))) hz')).elim
    · exact inferInstanceAs
        (IsIso ((ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).map g))
  have : Epi (σ N) := by
    rw [← image.fac (σ N)]
    have : Epi ι := inferInstance
    exact epi_comp _ _
  exact ⟨N, fun i ↦ (seq i).1, fun i ↦ (seq i).2, fun i ↦ hirr i, fun i ↦ hmono i, this⟩

/-- **Geometric constituents are subsheaves** (semisimplicity half of the sheaf-theoretic
Clifford theorem). Let `X̄` be irreducible and `F` an irreducible lisse Weil sheaf on `X`. If a
lisse subsheaf `B` of the underlying sheaf `F̄` surjects onto an irreducible lisse sheaf `A`,
then `A` embeds into `F̄`. -/
theorem IsIrreducibleLisse.exists_mono_of_isIrreducibleAdicLocalSystem {F : WeilSheaf k₀ l X}
    (hF : F.IsIrreducibleLisse)
    {A B : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hA : IsIrreducibleAdicLocalSystem A) (hB : IsAdicLisseSheaf B)
    (i : B ⟶ F.obj.carrier) [Mono i] (p : B ⟶ A) [Epi p] :
    ∃ m : A ⟶ F.obj.carrier, Mono m := by
  obtain ⟨N, S, m, hS, hm, hσ⟩ := hF.exists_epi_biproduct_desc
  have hP : IsAdicLisseSheaf (pullback (biproduct.desc m) i) :=
    (((IsAdicLisseSheaf.biproduct_fin N _ fun i ↦ (hS i).1).biprod
      hB).kernel_cokernel_of_irreducibleSpace hF.1 (biprod.desc (biproduct.desc m) (-i))).1.of_iso
      (IsLimit.conePointUniqueUpToIso
        (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct (biproduct.desc m) i)
        (kernelIsKernel _)).symm
  obtain ⟨k, g, hg⟩ := hA.exists_ne_zero_of_mono_of_epi N S hS
    (pullback (biproduct.desc m) i) hP (pullback.fst _ _) (pullback.snd _ _ ≫ p)
  have := (hS k).isIso_of_ne_zero hA g hg
  exact ⟨inv g ≫ m k, inferInstance⟩

end AlgebraicGeometry.WeilSheaf
