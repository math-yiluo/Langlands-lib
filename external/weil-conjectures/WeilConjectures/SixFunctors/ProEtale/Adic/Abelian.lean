/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.Extension
public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix
public import WeilConjectures.Mathlib.Topology.Constructible
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Kernels and cokernels of constructible `ℓ`-adic sheaves

A morphism `ψ : ℚ̄_ℓ,Tⁿ ⟶ ℚ̄_ℓ,Tᵐ` of finite free modules is a matrix of locally finite continuous
functions on `T` (`AlgebraicGeometry.ProEtale.AdicSheaf.unitMatrix`), and has a rank at every
point of `T`. If this rank is constant, then locally on `T` the morphism is equivalent to
`[[1, 0], [0, 0]]`, so its kernel and cokernel are lisse
(`AlgebraicGeometry.ProEtale.AdicSheaf.isAdicLisseSheaf_kernel_cokernel_of_rank_eq`).

For a morphism `φ` of lisse sheaves on `Y`, the rank of `φ` at a point does not depend on the
trivialisation used to compute it
(`AlgebraicGeometry.ProEtale.AdicSheaf.rank_eq_of_apply_eq`), is lower semicontinuous, and
descends to `Y` along the pro-étale cover
(`AlgebraicGeometry.Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage`). On the open
subscheme where it is maximal the kernel and cokernel of `φ` are lisse
(`AlgebraicGeometry.ProEtale.exists_nonempty_isAdicLisseSheaf_kernel_cokernel`), and Noetherian
induction gives finite stratifications on which they are lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isAdicStratifiedLisseSheaf_kernel_cokernel`).

Refining stratifications, kernels and cokernels of constructible sheaves on a locally Noetherian
scheme are constructible (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.kernel_cokernel`).
The Noetherian hypothesis is necessary: if the underlying space of `X` is a profinite set without
isolated points, such as `ℤ_ℓ`, multiplication by the continuous function `t ↦ t` on `ℚ̄_ℓ,X` has
a cokernel supported at a single non-constructible point.

## Main results

- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.kernel_cokernel`, and the instances
  `(adicConstructibleSheaf l X).IsClosedUnderKernels` and
  `(adicConstructibleSheaf l X).IsClosedUnderCokernels` for `[IsLocallyNoetherian X]`.
-/

@[expose] public section

open CategoryTheory Limits

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T : Type*} [TopologicalSpace T] {κ ι : Type*} [Fintype κ]
  [Fintype ι]

set_option linter.unusedFintypeInType false in
/-- The rank of a matrix of locally finite functions is lower semicontinuous. -/
lemma isOpen_setOf_le_rank (M : Matrix κ ι (locallyFiniteFunctions l T)) (j : ℕ) :
    IsOpen {t | j ≤ (M.map (locallyFiniteFunctionsEval t)).rank} := by
  have : {t | j ≤ (M.map (locallyFiniteFunctionsEval t)).rank} =
      ⋃ (e₁ : Fin j → κ) (e₂ : Fin j → ι), {t | (M.submatrix e₁ e₂).det.1 t ≠ 0} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact M.le_rank_map_iff _ j
  rw [this]
  exact isOpen_iUnion fun e₁ ↦ isOpen_iUnion fun e₂ ↦
    isOpen_compl_singleton.preimage (M.submatrix e₁ e₂).det.1.continuous

end PadicAlgCl

universe u

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AdicSheaf

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- A finite free module over a finite index type is a free module over `Fin n`. -/
noncomputable def freeFinIso (ι : Type) [Fintype ι] (V : Scheme.{u}) :
    (⨁ fun _ : ι ↦ unit l V) ≅ ⨁ fun _ : Fin (Fintype.card ι) ↦ unit l V :=
  biproduct.whiskerEquiv (g := fun _ : Fin (Fintype.card ι) ↦ unit l V) (Fintype.equivFin ι)
    fun _ ↦ Iso.refl (unit l V)

/-- **Kernels and cokernels of constant rank are lisse.** A morphism of finite free
`ℚ̄_ℓ,T`-modules whose matrix of functions has the same rank at every point of `T` has lisse
kernel and cokernel. -/
theorem isAdicLisseSheaf_kernel_cokernel_of_rank_eq
    (ψ : (⨁ fun _ : ι ↦ unit l T) ⟶ ⨁ fun _ : κ ↦ unit l T) (r : ℕ)
    (hr : ∀ t, ((unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank = r) :
    IsAdicLisseSheaf (kernel ψ) ∧ IsAdicLisseSheaf (cokernel ψ) := by
  classical
  choose U ρ γ hρ hγ hU ht hfac using
    fun t ↦ PadicAlgCl.exists_isOpen_eq_mul (unitMatrix ψ) r hr t
  let O (t : T) : T.Opens := ⟨U t, hU t⟩
  have hR : Presieve.ofArrows (fun t ↦ (O t).toScheme) (fun t ↦ (O t).ι) ∈
      Scheme.proetalePrecoverage T :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).2
        ⟨fun x ↦ ⟨x, by simpa [O] using ht x⟩, fun _ ↦ inferInstance⟩)
  have key (t : T) : ∃ (P : Matrix κ κ _) (Q : Matrix ι ι _), IsUnit P.det ∧ IsUnit Q.det ∧
      unitMatrix ((freeUpperStarIso l ι (O t).ι).inv ≫ ((O t).ι)^*ᵃ[l].map ψ ≫
        (freeUpperStarIso l κ (O t).ι).hom) = P * (Matrix.fromBlocks 1 0 0 0 :
          Matrix (Fin r ⊕ {i // i ∉ Set.range (ρ t)})
            (Fin r ⊕ {j // j ∉ Set.range (γ t)}) _).reindex
            (PadicAlgCl.sumComplEquiv (ρ t) (hρ t)).symm
            (PadicAlgCl.sumComplEquiv (γ t) (hγ t)).symm * Q := by
    obtain ⟨P, Q, hP, hQ, h⟩ := hfac t (O t).ι.base.hom (by simp [O])
    exact ⟨P, Q, hP, hQ, (unitMatrix_adicUpperStar _ ψ).trans h⟩
  refine ⟨⟨_, hR, ?_⟩, ⟨_, hR, ?_⟩⟩ <;> rintro _ _ ⟨t⟩ <;>
    obtain ⟨P, Q, hP, hQ, h⟩ := key t <;>
    have hconj := eq_blockMap_of_unitMatrix_eq _ P Q h <;>
    have := isIso_ofUnitMatrix P hP <;> have := isIso_ofUnitMatrix Q hQ
  · exact ⟨_, ⟨PreservesKernel.iso ((O t).ι)^*ᵃ[l] ψ ≪≫
      (kernelIsIsoComp (freeUpperStarIso l ι (O t).ι).inv _ ≪≫ kernelCompMono _
        (freeUpperStarIso l κ (O t).ι).hom).symm ≪≫ kernelIsoOfEq hconj ≪≫
      kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _ ≪≫ kernelBlockMapIso _ _ _ _ ≪≫
      freeFinIso _ _⟩⟩
  · exact ⟨_, ⟨PreservesCokernel.iso ((O t).ι)^*ᵃ[l] ψ ≪≫
      (cokernelEpiComp (freeUpperStarIso l ι (O t).ι).inv _ ≪≫ cokernelCompIsIso _
        (freeUpperStarIso l κ (O t).ι).hom).symm ≪≫ cokernelIsoOfEq hconj ≪≫
      cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ cokernelBlockMapIso _ _ _ _ ≪≫
      freeFinIso _ _⟩⟩

section Rank

variable {P : Scheme.{u}} {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

/-- The pointwise rank of a morphism of finite free modules is invariant under composition with
isomorphisms. -/
lemma rank_unitMatrix_eq_of_eq_comp
    (ψ₁ : (⨁ fun _ : ι ↦ unit l P) ⟶ ⨁ fun _ : κ ↦ unit l P)
    (ψ₂ : (⨁ fun _ : ι' ↦ unit l P) ⟶ ⨁ fun _ : κ' ↦ unit l P)
    (α : (⨁ fun _ : ι' ↦ unit l P) ≅ ⨁ fun _ : ι ↦ unit l P)
    (β : (⨁ fun _ : κ ↦ unit l P) ≅ ⨁ fun _ : κ' ↦ unit l P)
    (h : ψ₂ = α.hom ≫ ψ₁ ≫ β.hom) (t : P) :
    ((unitMatrix ψ₂).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank =
      ((unitMatrix ψ₁).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank := by
  have h' : ψ₁ = α.inv ≫ ψ₂ ≫ β.inv := by
    rw [h, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine le_antisymm ?_ ?_
  · rw [h, unitMatrix_comp, unitMatrix_comp,
      Matrix.map_mul (f := PadicAlgCl.locallyFiniteFunctionsEval t),
      Matrix.map_mul (f := PadicAlgCl.locallyFiniteFunctionsEval t)]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · rw [h', unitMatrix_comp, unitMatrix_comp,
      Matrix.map_mul (f := PadicAlgCl.locallyFiniteFunctionsEval t),
      Matrix.map_mul (f := PadicAlgCl.locallyFiniteFunctionsEval t)]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

section Transport

variable {Y V : Scheme.{u}} {n : ℕ}

/-- Transport of a trivialisation `h^* F ≅ ℚ̄_ℓⁿ` along a morphism `g`. -/
noncomputable def trivPull {F : AdicSheaf l Y} (h : V ⟶ Y)
    (e : (h)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ unit l V) (g : P ⟶ V) :
    (g ≫ h)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ unit l P :=
  (adicUpperStarComp l g h).app F ≪≫ (g)^*ᵃ[l].mapIso e ≪≫ freeUpperStarIso l (Fin n) g

lemma trivPull_conj {F G : AdicSheaf l Y} (φ : F ⟶ G) (h : V ⟶ Y) {m : ℕ}
    (e : (h)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ unit l V)
    (e' : (h)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin m ↦ unit l V) (g : P ⟶ V) :
    (trivPull h e g).inv ≫ (g ≫ h)^*ᵃ[l].map φ ≫ (trivPull h e' g).hom =
      (freeUpperStarIso l (Fin n) g).inv ≫ (g)^*ᵃ[l].map (e.inv ≫ (h)^*ᵃ[l].map φ ≫ e'.hom) ≫
        (freeUpperStarIso l (Fin m) g).hom := by
  have := (adicUpperStarComp l g h).hom.naturality φ
  simp only [Functor.comp_map] at this
  simp only [trivPull, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc, Functor.map_comp]
  rw [reassoc_of% this, Iso.inv_hom_id_app_assoc]

end Transport

section Descent

variable {Y V V' : Scheme.{u}} {F G : AdicSheaf l Y} (φ : F ⟶ G) {n m n' m' : ℕ}

/-- **The pointwise rank of a morphism of lisse sheaves descends.** Trivialising a morphism of
sheaves over two weakly étale maps, the matrices of functions have the same rank at points with
the same image. -/
lemma rank_eq_of_apply_eq (f : V ⟶ Y) (f' : V' ⟶ Y) [WeaklyEtale f] [WeaklyEtale f']
    (e : (f)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ unit l V)
    (e₂ : (f)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin m ↦ unit l V)
    (e' : (f')^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n' ↦ unit l V')
    (e₂' : (f')^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin m' ↦ unit l V')
    (v : V) (v' : V') (hvv' : f v = f' v') :
    ((unitMatrix (e.inv ≫ (f)^*ᵃ[l].map φ ≫ e₂.hom)).map
        (PadicAlgCl.locallyFiniteFunctionsEval v)).rank =
      ((unitMatrix (e'.inv ≫ (f')^*ᵃ[l].map φ ≫ e₂'.hom)).map
        (PadicAlgCl.locallyFiniteFunctionsEval v')).rank := by
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback v v' hvv'
  have key := conj_eq_comp_conj (adicUpperStarCongr l (pullback.condition (f := f) (g := f'))) φ
    (trivPull f e (pullback.fst f f')) (trivPull f e₂ (pullback.fst f f'))
    (trivPull f' e' (pullback.snd f f')) (trivPull f' e₂' (pullback.snd f f'))
  rw [trivPull_conj, trivPull_conj] at key
  have hX := rank_unitMatrix_eq_of_eq_comp _ _ _ _ key w
  rw [unitMatrix_adicUpperStar, unitMatrix_adicUpperStar] at hX
  have e1 {W P' : Scheme.{u}} {a b : ℕ} (M : Matrix (Fin a) (Fin b) _) (g : P' ⟶ W) (w : P') :
      (M.map (PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom)).map
        (PadicAlgCl.locallyFiniteFunctionsEval w) =
        M.map (PadicAlgCl.locallyFiniteFunctionsEval (g w)) := by
    ext; rfl
  rw [e1, e1, hw, hw'] at hX
  exact hX

end Descent

end Rank

end AdicSheaf

section Generic

lemma isAdicLisseSheaf_kernel_of_eq_comp {Y : Scheme.{u}} {A B A' B' : AdicSheaf l Y}
    (ψ : A ⟶ B) (X : A' ⟶ B') (α : A' ≅ A) (β : B ≅ B') (h : X = α.hom ≫ ψ ≫ β.hom)
    (hX : IsAdicLisseSheaf (kernel X) ∧ IsAdicLisseSheaf (cokernel X)) :
    IsAdicLisseSheaf (kernel ψ) ∧ IsAdicLisseSheaf (cokernel ψ) :=
  ⟨hX.1.of_iso (kernelIsoOfEq h ≪≫ kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _),
    hX.2.of_iso (cokernelIsoOfEq h ≪≫ cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _)⟩

attribute [local instance] Abelian.hasFiniteBiproducts

open AdicSheaf in
/-- **Generic lisseness of kernels and cokernels.** A morphism of lisse sheaves on a nonempty
quasi-compact scheme has lisse kernel and cokernel over a nonempty open subscheme: the open
subscheme where the pointwise rank is maximal. -/
theorem exists_nonempty_isAdicLisseSheaf_kernel_cokernel {Y : Scheme.{u}} [CompactSpace Y]
    [Nonempty Y] {F G : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G)
    (φ : F ⟶ G) : ∃ U : Y.Opens, (U : Set Y).Nonempty ∧
      IsAdicLisseSheaf (kernel ((U.ι)^*ᵃ[l].map φ)) ∧
        IsAdicLisseSheaf (cokernel ((U.ι)^*ᵃ[l].map φ)) := by
  classical
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨R', hR', hR'G⟩ := hG
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨ι', V', f', rfl⟩ := R'.exists_eq_ofArrows
  have hW := Precoverage.comp_mem_coverings f hR (fun i j ↦ pullback.fst (f i) (f' j))
    (fun i ↦ Precoverage.mem_coverings_of_isPullback f' hR' (f i) _ _
      fun j ↦ IsPullback.of_hasPullback (f i) (f' j))
  let W (k : Σ _ : ι, ι') : Scheme.{u} := pullback (f k.1) (f' k.2)
  let g (k : Σ _ : ι, ι') : W k ⟶ Y := pullback.fst (f k.1) (f' k.2) ≫ f k.1
  change Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage Y at hW
  have hgw (k) : WeaklyEtale (g k) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hW (.mk k)
  choose n e using fun i ↦ hRF (f i) (.mk i)
  choose m e' using fun j ↦ hR'G (f' j) (.mk j)
  let eF (k : Σ _ : ι, ι') : (g k)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin (n k.1) ↦ unit l (W k) :=
    trivPull (f k.1) (e k.1).some (pullback.fst (f k.1) (f' k.2))
  let eG (k : Σ _ : ι, ι') : (g k)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin (m k.2) ↦ unit l (W k) :=
    (adicUpperStarCongr l pullback.condition).app G ≪≫
      trivPull (f' k.2) (e' k.2).some (pullback.snd (f k.1) (f' k.2))
  let rk (k : Σ _ : ι, ι') (v : W k) : ℕ :=
    ((unitMatrix ((eF k).inv ≫ (g k)^*ᵃ[l].map φ ≫ (eG k).hom)).map
      (PadicAlgCl.locallyFiniteFunctionsEval v)).rank
  have hfc (k k' : Σ _ : ι, ι') (v : W k) (v' : W k') (h : g k v = g k' v') :
      rk k v = rk k' v' :=
    rank_eq_of_apply_eq φ (g k) (g k') (eF k) (eG k) (eF k') (eG k') v v' h
  have hsurj : ∀ y, ∃ k, y ∈ Set.range (g k) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hW)).1
  choose kk vv hvv using hsurj
  let Rk (y : Y) : ℕ := rk (kk y) (vv y)
  have hRk (k : Σ _ : ι, ι') (v : W k) : Rk (g k v) = rk k v :=
    hfc _ _ _ _ (hvv _)
  have hopen (j : ℕ) : IsOpen {y | j ≤ Rk y} := by
    refine Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage g hW _ fun k ↦ ?_
    have : (g k).base ⁻¹' {y | j ≤ Rk y} = {v | j ≤ rk k v} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      erw [hRk]
    rw [this]
    exact PadicAlgCl.isOpen_setOf_le_rank _ j
  -- a bound for the rank, from a finite subcover
  let E : PreZeroHypercover Y := ⟨_, W, g⟩
  have : QuasiCompactCover E := by
    have := hW.1
    rwa [show Presieve.ofArrows W g = E.presieve₀ from rfl,
      Scheme.presieve₀_mem_qcPrecoverage_iff] at this
  obtain ⟨N, a, Vs, -, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact E
    (U := ⊤) isCompact_univ
  let B := Finset.univ.sup fun i : Fin N ↦ n (a i).1
  have hB (y : Y) : Rk y ≤ B := by
    have : y ∈ ⋃ i, E.f (a i) '' (Vs i : Set _) := by rw [hcov]; trivial
    obtain ⟨i, v, -, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_image] using this
    change Rk (g (a i) v) ≤ B
    rw [hRk]
    refine (Matrix.rank_le_width _).trans ?_
    exact Finset.le_sup (f := fun i : Fin N ↦ n (a i).1) (Finset.mem_univ i)
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  let jmax := Nat.findGreatest (fun j ↦ ∃ y, Rk y = j) B
  have hmax (y : Y) : Rk y ≤ jmax := Nat.le_findGreatest (hB y) ⟨y, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y, Rk y = jmax :=
    Nat.findGreatest_spec (P := fun j ↦ ∃ y, Rk y = j) (hB y₀) ⟨y₀, rfl⟩
  let U : Y.Opens := ⟨{y | jmax ≤ Rk y}, hopen jmax⟩
  refine ⟨U, ⟨y₁, hy₁.ge⟩, ?_⟩
  -- the base change of the cover to `U`
  have hP := Precoverage.mem_coverings_of_isPullback g hW U.ι _ _
    fun k ↦ IsPullback.of_hasPullback U.ι (g k)
  have e1 {Z P' : Scheme.{u}} {a b : ℕ} (M : Matrix (Fin a) (Fin b) _) (q : P' ⟶ Z) (w : P') :
      (M.map (PadicAlgCl.locallyFiniteFunctionsComp l q.base.hom)).map
        (PadicAlgCl.locallyFiniteFunctionsEval w) =
        M.map (PadicAlgCl.locallyFiniteFunctionsEval (q w)) := by
    ext; rfl
  have hmem (k : Σ _ : ι, ι') :
      IsAdicLisseSheaf (kernel ((pullback.fst U.ι (g k))^*ᵃ[l].map ((U.ι)^*ᵃ[l].map φ))) ∧
      IsAdicLisseSheaf (cokernel ((pullback.fst U.ι (g k))^*ᵃ[l].map ((U.ι)^*ᵃ[l].map φ))) := by
    have key := conj_eq_comp_conj' ((adicUpperStarCongr l
      (pullback.condition (f := U.ι) (g := g k)).symm) ≪≫ adicUpperStarComp l _ _) φ
      (trivPull (g k) (eF k) (pullback.snd U.ι (g k)))
      (trivPull (g k) (eG k) (pullback.snd U.ι (g k)))
    rw [trivPull_conj] at key
    refine isAdicLisseSheaf_kernel_of_eq_comp _ _ _ _ key
      (isAdicLisseSheaf_kernel_cokernel_of_rank_eq _ jmax fun w ↦ ?_)
    rw [unitMatrix_adicUpperStar, e1]
    change rk k _ = jmax
    rw [← hRk, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact le_antisymm (hmax _) (pullback.fst U.ι (g k) w).2
  exact ⟨IsAdicLisseSheaf.of_presieve _ hP fun _ _ ⟨k⟩ ↦
      (hmem k).1.of_iso (PreservesKernel.iso _ _).symm,
    IsAdicLisseSheaf.of_presieve _ hP fun _ _ ⟨k⟩ ↦
      (hmem k).2.of_iso (PreservesCokernel.iso _ _).symm⟩

end Generic

section Stratification

open TopologicalSpace Topology

/-- **Stratified lisseness of kernels and cokernels.** A morphism of lisse sheaves on a scheme
whose underlying space is Noetherian has stratified lisse kernel and cokernel, by Noetherian
induction from the generic lisseness. -/
theorem IsAdicLisseSheaf.exists_stratification_kernel_cokernel {Y : Scheme.{u}}
    [NoetherianSpace Y] {F G : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G)
    (φ : F ⟶ G) (Z : Closeds Y) :
    ∃ (ι : Type) (_ : Finite ι) (S : ι → Scheme.{u}) (i : (k : ι) → S k ⟶ Y),
      (∀ k, IsImmersion (i k)) ∧ (∀ k, IsConstructible (Set.range (i k).base)) ∧
      (∀ k, Set.range (i k).base ⊆ Z) ∧ (∀ y ∈ Z, ∃! k, y ∈ Set.range (i k).base) ∧
      ∀ k, IsAdicLisseSheaf ((i k)^*ᵃ[l].obj (kernel φ)) ∧
        IsAdicLisseSheaf ((i k)^*ᵃ[l].obj (cokernel φ)) := by
  induction Z using WellFoundedLT.induction with
  | ind Z IH =>
  by_cases hZ : (Z : Set Y) = ∅
  · refine ⟨Empty, inferInstance, Empty.elim, fun k ↦ k.elim, fun k ↦ k.elim, fun k ↦ k.elim,
      fun k ↦ k.elim, fun y hy ↦ absurd (hZ ▸ hy : y ∈ (∅ : Set Y)) id, fun k ↦ k.elim⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let iZ := I.subschemeι
  have hrange : Set.range iZ.base = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have : CompactSpace I.subscheme := iZ.isClosedEmbedding.compactSpace
  obtain ⟨y₀, hy₀⟩ := Set.nonempty_iff_ne_empty.2 hZ
  have : Nonempty I.subscheme := by
    obtain ⟨z, -⟩ := hrange.symm ▸ hy₀
    exact ⟨z⟩
  obtain ⟨U, hUne, hker, hcok⟩ := exists_nonempty_isAdicLisseSheaf_kernel_cokernel
    (hF.upperStar iZ) (hG.upperStar iZ) ((iZ)^*ᵃ[l].map φ)
  let Z' : Closeds Y := ⟨iZ.base '' (U : Set I.subscheme)ᶜ,
    iZ.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
  have hZ' : (Z' : Set Y) = (Z : Set Y) \ iZ.base '' U := by
    rw [← hrange, ← Set.image_univ, ← Set.image_sdiff iZ.isClosedEmbedding.injective,
      ← Set.compl_eq_univ_sdiff]
    rfl
  have hZ'Z : Z' < Z := by
    refine lt_of_le_of_ne (fun y hy ↦ ?_) fun h ↦ ?_
    · have hy' : y ∈ (Z' : Set Y) := hy
      rw [hZ'] at hy'
      exact hy'.1
    · obtain ⟨u, hu⟩ := hUne
      have : iZ.base u ∈ (Z' : Set Y) := by rw [h, ← hrange]; exact Set.mem_range_self u
      rw [hZ'] at this
      exact this.2 ⟨u, hu, rfl⟩
  obtain ⟨ι', _, S', i', himm, hc, hsub, huniq, hlisse⟩ := IH Z' hZ'Z
  have hrU : Set.range (U.ι ≫ iZ).base = iZ.base '' U := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  refine ⟨Option ι', inferInstance, fun k ↦ k.elim U.toScheme S',
    fun k ↦ match k with | none => U.ι ≫ iZ | some k => i' k, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | k)
    · exact inferInstanceAs (IsImmersion (U.ι ≫ iZ))
    · exact himm k
  · rintro (_ | k)
    · change IsConstructible (Set.range (U.ι ≫ iZ).base)
      have hsd : iZ.base '' U = (Z : Set Y) \ Z' := by
        rw [hZ', Set.sdiff_sdiff_cancel_left]
        exact hrange ▸ Set.image_subset_range _ _
      rw [hrU, hsd]
      exact Z.isClosed.isConstructible_of_noetherianSpace.sdiff
        Z'.isClosed.isConstructible_of_noetherianSpace
    · exact hc k
  · rintro (_ | k)
    · change Set.range (U.ι ≫ iZ).base ⊆ Z
      rw [hrU, ← hrange]
      exact Set.image_subset_range _ _
    · exact (hsub k).trans hZ'Z.le
  · intro y hy
    by_cases hy' : y ∈ Z'
    · obtain ⟨k, hk, hk'⟩ := huniq y hy'
      refine ⟨some k, hk, ?_⟩
      rintro (_ | k') hk''
      · change y ∈ Set.range (U.ι ≫ iZ).base at hk''
        rw [hrU] at hk''
        have : y ∈ (Z' : Set Y) := hy'
        rw [hZ'] at this
        exact absurd hk'' this.2
      · exact congrArg some (hk' k' hk'')
    · refine ⟨none, ?_, ?_⟩
      · change y ∈ Set.range (U.ι ≫ iZ).base
        rw [hrU]
        by_contra h
        exact hy' (show y ∈ (Z' : Set Y) by rw [hZ']; exact ⟨hy, h⟩)
      · rintro (_ | k') hk''
        · rfl
        · exact absurd (hsub k' hk'') hy'
  · rintro (_ | k)
    · exact ⟨hker.of_iso ((adicUpperStarComp l U.ι iZ).app (kernel φ) ≪≫
          (U.ι)^*ᵃ[l].mapIso (PreservesKernel.iso (iZ)^*ᵃ[l] φ) ≪≫
          PreservesKernel.iso (U.ι)^*ᵃ[l] _).symm,
        hcok.of_iso ((adicUpperStarComp l U.ι iZ).app (cokernel φ) ≪≫
          (U.ι)^*ᵃ[l].mapIso (PreservesCokernel.iso (iZ)^*ᵃ[l] φ) ≪≫
          PreservesCokernel.iso (U.ι)^*ᵃ[l] _).symm⟩
    · exact hlisse k

/-- A morphism of lisse sheaves on a scheme with Noetherian underlying space has stratified lisse
kernel and cokernel. -/
theorem IsAdicLisseSheaf.isAdicStratifiedLisseSheaf_kernel_cokernel {Y : Scheme.{u}}
    [NoetherianSpace Y] {F G : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G)
    (φ : F ⟶ G) :
    IsAdicStratifiedLisseSheaf (kernel φ) ∧ IsAdicStratifiedLisseSheaf (cokernel φ) := by
  obtain ⟨ι, hι, S, i, himm, hc, -, huniq, hlisse⟩ :=
    exists_stratification_kernel_cokernel hF hG φ ⊤
  exact ⟨⟨ι, hι, S, i, himm, hc, fun y ↦ huniq y trivial, fun k ↦ (hlisse k).1⟩,
    ⟨ι, hι, S, i, himm, hc, fun y ↦ huniq y trivial, fun k ↦ (hlisse k).2⟩⟩

end Stratification

section Constructible

open TopologicalSpace Topology

/-- Refining a stratification by stratifications of its strata: a sheaf whose restrictions to
the strata of a finite stratification of a Noetherian scheme are stratified lisse is stratified
lisse. -/
lemma IsAdicStratifiedLisseSheaf.of_stratification {V : Scheme.{u}} [NoetherianSpace V]
    {K : AdicSheaf l V} {ι : Type} [Finite ι] (Z : ι → Scheme.{u}) (i : (k : ι) → Z k ⟶ V)
    (himm : ∀ k, IsImmersion (i k)) (huniq : ∀ y, ∃! k, y ∈ Set.range (i k).base)
    (h : ∀ k, IsAdicStratifiedLisseSheaf ((i k)^*ᵃ[l].obj K)) :
    IsAdicStratifiedLisseSheaf K := by
  choose κ hκ S s hs hsc hsu hsl using h
  refine ⟨Σ k, κ k, inferInstance, fun p ↦ S p.1 p.2, fun p ↦ s p.1 p.2 ≫ i p.1,
    fun p ↦ inferInstance, fun p ↦ ?_, fun y ↦ ?_, fun p ↦ ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (hsc p.1 p.2).image_of_isEmbedding (i p.1).isEmbedding (i p.1).isLocallyClosed_range
  · obtain ⟨k, ⟨z, rfl⟩, hk⟩ := huniq y
    obtain ⟨m, hm, hm'⟩ := hsu k z
    refine ⟨⟨k, m⟩, ?_, ?_⟩
    · obtain ⟨w, rfl⟩ := hm
      exact ⟨w, rfl⟩
    · rintro ⟨k', m'⟩ ⟨w, hw⟩
      change (s k' m' ≫ i k') w = _ at hw
      rw [Scheme.Hom.comp_apply] at hw
      obtain rfl : k' = k := hk k' ⟨_, hw⟩
      obtain rfl := (i k').isEmbedding.injective hw
      obtain rfl : m' = m := hm' m' ⟨w, rfl⟩
      rfl
  · exact (hsl p.1 p.2).of_iso ((adicUpperStarComp l _ _).app K).symm

/-- Two stratified lisse sheaves are lisse on the strata of a common stratification. -/
lemma IsAdicStratifiedLisseSheaf.exists_common {V : Scheme.{u}} {F G : AdicSheaf l V}
    (hF : IsAdicStratifiedLisseSheaf F) (hG : IsAdicStratifiedLisseSheaf G) :
    ∃ (ι : Type) (_ : Finite ι) (Z : ι → Scheme.{u}) (i : (k : ι) → Z k ⟶ V),
      (∀ k, IsImmersion (i k)) ∧ (∀ y, ∃! k, y ∈ Set.range (i k).base) ∧
      ∀ k, IsAdicLisseSheaf ((i k)^*ᵃ[l].obj F) ∧ IsAdicLisseSheaf ((i k)^*ᵃ[l].obj G) := by
  obtain ⟨ι, hι, Z, i, hi, -, hcover, h⟩ := hF
  obtain ⟨ι', hι', Z', i', hi', -, hcover', h'⟩ := hG
  refine ⟨ι × ι', inferInstance, fun k ↦ pullback (i k.1) (i' k.2),
    fun k ↦ pullback.fst (i k.1) (i' k.2) ≫ i k.1, fun k ↦ inferInstance, fun x ↦ ?_,
    fun k ↦ ⟨((h k.1).upperStar _).of_iso ((adicUpperStarComp l _ _).app F).symm, ?_⟩⟩
  · obtain ⟨k, ⟨z, hz⟩, hk⟩ := hcover x
    obtain ⟨k', ⟨z', hz'⟩, hk'⟩ := hcover' x
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback z z' (hz.trans hz'.symm)
    refine ⟨(k, k'), ⟨t, by rw [Scheme.Hom.comp_apply, ht, hz]⟩, fun m ⟨t', ht'⟩ ↦ ?_⟩
    refine Prod.ext (hk m.1 ⟨_, ht'⟩) (hk' m.2 ⟨pullback.snd (i m.1) (i' m.2) t', ?_⟩)
    rw [← ht', ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  · exact (((h' k.2).upperStar (pullback.snd (i k.1) (i' k.2))).of_iso
      ((adicUpperStarCompIso l pullback.condition.symm).app G)).of_iso
      ((adicUpperStarComp l (pullback.fst (i k.1) (i' k.2)) (i k.1)).app G).symm

/-- **Kernels and cokernels of constructible sheaves are constructible** (Bhatt–Scholze, §6.8),
on a locally Noetherian scheme: on a common stratification of an affine open neighbourhood both
sheaves are lisse, and the kernel and cokernel of a morphism of lisse sheaves are stratified
lisse. -/
theorem IsAdicConstructibleSheaf.kernel_cokernel {X : Scheme.{u}} [IsLocallyNoetherian X]
    {F G : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F) (hG : IsAdicConstructibleSheaf G)
    (φ : F ⟶ G) :
    IsAdicConstructibleSheaf (kernel φ) ∧ IsAdicConstructibleSheaf (cokernel φ) := by
  have key (x : X) : ∃ V : X.Opens, x ∈ V ∧
      IsAdicStratifiedLisseSheaf ((V.ι)^*ᵃ[l].obj (kernel φ)) ∧
      IsAdicStratifiedLisseSheaf ((V.ι)^*ᵃ[l].obj (cokernel φ)) := by
    obtain ⟨W, j, hj, ⟨w, hw⟩, hFs⟩ := hF x
    obtain ⟨W', j', hj', ⟨w', hw'⟩, hGs⟩ := hG x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (⟨⟨w, hw⟩, ⟨w', hw'⟩⟩ : x ∈ Set.range j.base ∩ Set.range j'.base)
      (j.isOpenEmbedding.isOpen_range.inter j'.isOpenEmbedding.isOpen_range)
    have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
    let a := IsOpenImmersion.lift j (Scheme.Opens.ι V) (by
      rw [Scheme.Opens.range_ι]; exact hVsub.trans Set.inter_subset_left)
    let a' := IsOpenImmersion.lift j' (Scheme.Opens.ι V) (by
      rw [Scheme.Opens.range_ι]; exact hVsub.trans Set.inter_subset_right)
    have hFV : IsAdicStratifiedLisseSheaf (((Scheme.Opens.ι V))^*ᵃ[l].obj F) :=
      (hFs.upperStar a).of_iso (((adicUpperStarComp l a j).app F).symm ≪≫
        (adicUpperStarCongr l (IsOpenImmersion.lift_fac _ _ _)).app F)
    have hGV : IsAdicStratifiedLisseSheaf (((Scheme.Opens.ι V))^*ᵃ[l].obj G) :=
      (hGs.upperStar a').of_iso (((adicUpperStarComp l a' j').app G).symm ≪≫
        (adicUpperStarCongr l (IsOpenImmersion.lift_fac _ _ _)).app G)
    obtain ⟨ι, _, Z, i, himm, huniq, hl⟩ := hFV.exists_common hGV
    refine ⟨V, hxV, IsAdicStratifiedLisseSheaf.of_stratification Z i himm huniq fun k ↦ ?_,
      IsAdicStratifiedLisseSheaf.of_stratification Z i himm huniq fun k ↦ ?_⟩ <;>
      have : NoetherianSpace (Z k) := (i k).isEmbedding.isInducing.noetherianSpace <;>
      have hk := IsAdicLisseSheaf.isAdicStratifiedLisseSheaf_kernel_cokernel (hl k).1 (hl k).2
        ((i k)^*ᵃ[l].map (((Scheme.Opens.ι V))^*ᵃ[l].map φ))
    · exact hk.1.of_iso ((i k)^*ᵃ[l].mapIso (PreservesKernel.iso ((Scheme.Opens.ι V))^*ᵃ[l] φ) ≪≫
        PreservesKernel.iso (i k)^*ᵃ[l] _).symm
    · exact hk.2.of_iso ((i k)^*ᵃ[l].mapIso (PreservesCokernel.iso ((Scheme.Opens.ι V))^*ᵃ[l] φ) ≪≫
        PreservesCokernel.iso (i k)^*ᵃ[l] _).symm
  refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩ <;> obtain ⟨V, hxV, hk, hc⟩ := key x
  · exact ⟨V, V.ι, inferInstance, ⟨⟨x, hxV⟩, rfl⟩, hk⟩
  · exact ⟨V, V.ι, inferInstance, ⟨⟨x, hxV⟩, rfl⟩, hc⟩

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **Kernels of constructible sheaves are constructible** on a locally Noetherian scheme
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.kernel_cokernel`). -/
instance : (adicConstructibleSheaf l X).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (adicConstructibleSheaf l X).prop_of_iso
      ((kernelIsKernel f).conePointUniqueUpToIso hk)
      (IsAdicConstructibleSheaf.kernel_cokernel hX hY f).1

/-- **Cokernels of constructible sheaves are constructible** on a locally Noetherian scheme
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.kernel_cokernel`). -/
instance : (adicConstructibleSheaf l X).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (adicConstructibleSheaf l X).prop_of_iso
      ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
      (IsAdicConstructibleSheaf.kernel_cokernel hX hY f).2

end Constructible

end AlgebraicGeometry.ProEtale
