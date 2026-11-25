/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse
public import WeilConjectures.WeilSheaf.Category

/-!
# The trivial geometric constituent of an irreducible Weil sheaf

Let `X` be a `k₀`-scheme whose geometric fiber `X̄` is irreducible, and `F` a nonzero irreducible
lisse Weil sheaf on `X`. If the trivial sheaf `ℚ̄_ℓ` is a geometric constituent of `F`, that is
a quotient of a lisse subsheaf of the underlying sheaf `F̄` on `X̄`, then `F̄` is constant: a
finite direct sum of copies of `ℚ̄_ℓ`
(`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_iso_biproduct_unit`).

This is the sheaf-theoretic form of Clifford's theorem for the normal subgroup `π₁(X̄)` of the
Weil group. The lisse sheaves on the irreducible `X̄` form an abelian category in which every
object has finite length, measured by the dimension of a geometric stalk
(`WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse`), and the Frobenius pullback
`Fr^*` is an autoequivalence of it.

- Let `S ⊆ F̄` be a lisse subsheaf of minimal positive rank; it is irreducible. Its Frobenius
  translates `S_n = φ(Fr^* S_{n-1})` are irreducible lisse subsheaves of `F̄`.
- The sums `S_0 + ⋯ + S_N` increase and stabilise; the stable sum `T` is carried into itself by
  `φ ∘ Fr^*`, hence onto itself by rank, so it is a Weil subsheaf, and `T = F̄` by the
  irreducibility of `F`. Thus `F̄` is a quotient of `S_0 ⊕ ⋯ ⊕ S_N`.
- A subquotient `ℚ̄_ℓ` of `S_0 ⊕ ⋯ ⊕ S_N` forces some `S_n ≅ ℚ̄_ℓ`, by induction on `N`; then
  `S ≅ ℚ̄_ℓ` and every `S_n ≅ Fr^{*n} ℚ̄_ℓ ≅ ℚ̄_ℓ`.
- A lisse quotient of a finite sum of copies of the irreducible `ℚ̄_ℓ` is again such a sum.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The Frobenius pullback of a lisse sheaf is lisse: it is the pullback along the geometric
Galois Frobenius. -/
theorem isAdicLisseSheaf_frobeniusPullback_obj
    {H : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (hH : IsAdicLisseSheaf H) :
    IsAdicLisseSheaf ((frobeniusPullback k₀ l X).obj H) :=
  (hH.upperStar _).of_iso
    ((adicUpperStarIsoLowerStarInv l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).app H)

/-- A sheaf whose Frobenius pullback is lisse is lisse. -/
theorem isAdicLisseSheaf_of_frobeniusPullback_obj
    {H : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hH : IsAdicLisseSheaf ((frobeniusPullback k₀ l X).obj H)) : IsAdicLisseSheaf H :=
  let Fr := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
  (hH.upperStar Fr.inv).of_iso ((adicUpperStarIsoLowerStarInv l Fr.symm).app _ ≪≫
    ((adicLowerStarEquivalence l Fr.symm).unitIso.app H).symm)

/-- The Frobenius pullback of the constant sheaf `ℚ̄_ℓ` is `ℚ̄_ℓ`. -/
noncomputable def frobeniusPullbackUnitIso :
    (frobeniusPullback k₀ l X).obj
        (AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≅
      AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  adicLowerStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm


variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The Frobenius pullback of a lisse sheaf has the same rank: its stalk at `s` is the stalk of
the sheaf at `s ≫ Fr`. -/
theorem finrank_geometricStalkFunctor_frobeniusPullback_obj
    [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    {H : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (hH : IsAdicLisseSheaf H)
    (s : Spec (.of K) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((geometricStalkFunctor l s).obj ((frobeniusPullback k₀ l X).obj H))) =
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((geometricStalkFunctor l s).obj H)) := by
  let Fr := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
  let e : (s)^*ᵃ[l].obj ((frobeniusPullback k₀ l X).obj H) ≅ (s ≫ Fr.hom)^*ᵃ[l].obj H :=
    (s)^*ᵃ[l].mapIso ((adicUpperStarIsoLowerStarInv l Fr).app H).symm ≪≫
      ((adicUpperStarComp l s Fr.hom).app H).symm
  rw [← hH.finrank_geometricStalkFunctor_eq (s ≫ Fr.hom) s]
  exact ((AdicSheaf.forget _ ⋙ Sheaf.Γ _ _ ⋙ WeilCoefficients.toModuleCat l).mapIso
    e).toLinearEquiv.finrank_eq

/-- The Frobenius pullback of an irreducible local system is irreducible: it is an
autoequivalence preserving lisse sheaves in both directions. -/
theorem isIrreducibleAdicLocalSystem_frobeniusPullback_obj
    {H : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hH : IsIrreducibleAdicLocalSystem H) :
    IsIrreducibleAdicLocalSystem ((frobeniusPullback k₀ l X).obj H) := by
  let eqv := adicLowerStarEquivalence l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm
  change IsIrreducibleAdicLocalSystem (eqv.functor.obj H)
  refine ⟨isAdicLisseSheaf_frobeniusPullback_obj hH.1, fun hz ↦ hH.2.1 ?_,
    fun A j _ hA ↦ ?_⟩
  · exact (eqv.inverse.map_isZero hz).of_iso (eqv.unitIso.app H)
  · have hA' : IsAdicLisseSheaf (eqv.inverse.obj A) :=
      isAdicLisseSheaf_of_frobeniusPullback_obj (hA.of_iso (eqv.counitIso.app A).symm)
    rcases hH.2.2 _ (eqv.inverse.map j ≫ (eqv.unitIso.app H).inv) inferInstance hA' with h | h
    · exact Or.inl ((eqv.functor.map_isZero h).of_iso (eqv.counitIso.app A).symm)
    · have : IsIso (eqv.inverse.map j) := by
        have := IsIso.comp_isIso' h (inferInstance : IsIso (eqv.unitIso.app H).hom)
        simpa using this
      exact Or.inr (isIso_of_reflects_iso j eqv.inverse)

variable [Fact (ringChar k₀ ≠ l)]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

/-- **The trivial geometric constituent of an irreducible Weil sheaf** (sheaf-theoretic Clifford
theorem). Let `X̄` be irreducible and `F` an irreducible lisse Weil sheaf on `X`. If a lisse
subsheaf `B` of the underlying sheaf `F̄` surjects onto `ℚ̄_ℓ`, then `F̄` is a finite direct sum of
copies of `ℚ̄_ℓ`. -/
theorem IsIrreducibleLisse.exists_iso_biproduct_unit {F : WeilSheaf k₀ l X}
    (hF : F.IsIrreducibleLisse)
    {B : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (hB : IsAdicLisseSheaf B)
    (i : B ⟶ F.obj.carrier) [Mono i]
    (p : B ⟶ AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) [Epi p] :
    ∃ n : ℕ, Nonempty (F.obj.carrier ≅
      ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
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
  let incl (N : ℕ) : (⨁ fun i : Fin N ↦ (seq i).1) ⟶ ⨁ fun i : Fin (N + 1) ↦ (seq i).1 :=
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
    simp only [biproduct.ι_desc_assoc, comp_zero, ← Functor.map_comp_assoc, σ, biproduct.ι_desc]
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
  -- the trivial constituent is some `S_k`
  have hP : IsAdicLisseSheaf (pullback (σ N) i) :=
    (((hW N).biprod hB).kernel_cokernel_of_irreducibleSpace hFl
      (biprod.desc (σ N) (-i))).1.of_iso
      (IsLimit.conePointUniqueUpToIso
        (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct (σ N) i)
        (kernelIsKernel _)).symm
  have hU := isIrreducibleAdicLocalSystem_unit (l := l) (Y := Y)
  obtain ⟨k, g', hg'⟩ := hU.exists_ne_zero_of_mono_of_epi N (fun i ↦ (seq i).1) (fun i ↦ hirr i)
    (pullback (σ N) i) hP (pullback.fst _ _) (pullback.snd _ _ ≫ p)
  have := (hirr k).isIso_of_ne_zero hU g' hg'
  have hdown (n : ℕ) (e : (seq n).1 ≅ AdicSheaf.unit l Y) : Nonempty (S₀ ≅ AdicSheaf.unit l Y) := by
    induction n with
    | zero => exact ⟨e⟩
    | succ n ih => exact ih (E.preimageIso (e ≪≫ frobeniusPullbackUnitIso.symm))
  obtain ⟨e₀⟩ := hdown k (asIso g')
  have hup (n : ℕ) : Nonempty ((seq n).1 ≅ AdicSheaf.unit l Y) := by
    induction n with
    | zero => exact ⟨e₀⟩
    | succ n ih => exact ⟨E.mapIso ih.some ≪≫ frobeniusPullbackUnitIso⟩
  exact exists_iso_biproduct_unit_of_epi N (fun i ↦ (seq i).1) (fun i ↦ hup i) _ hFl (σ N)

end AlgebraicGeometry.WeilSheaf
