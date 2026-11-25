/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk

/-!
# Lisse `ℓ`-adic sheaves on locally Noetherian schemes form an abelian category

A morphism `φ : F ⟶ G` of lisse sheaves on `Y` becomes, on the members of a trivialising
pro-étale cover, a matrix of locally finite continuous functions; its pointwise rank descends to
a function on `Y` (`AlgebraicGeometry.ProEtale.AdicSheaf.rank_eq_of_apply_eq`) which is constant
along specializations: continuous functions to the Hausdorff space `ℚ̄_ℓ` are constant along
specializations, and flat morphisms lift generizations. On a locally Noetherian scheme such a
function is locally constant (`AlgebraicGeometry.isLocallyConstant_of_specializes`): on a
Noetherian open, the set where it takes a given value is the union of the finitely many
irreducible components it meets. Locally on the members of the cover, the matrix then has
constant rank, so the kernel and cokernel of `φ` are lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.kernel_cokernel`).

Similarly the rank of a trivialisation of a lisse sheaf `H` is constant along specializations,
so `H` vanishes as soon as its stalks vanish at geometric points over a point of each
irreducible component
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isZero_of_subsingleton_globalSections_upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace ZeroObject

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- In a Noetherian quasi-sober space, a set which is stable under specialization and
generalization is closed: it is the union of the finitely many irreducible components it
meets. -/
theorem TopologicalSpace.NoetherianSpace.isClosed_of_specializes_iff [NoetherianSpace X]
    [QuasiSober X] {S : Set X} (hS : ∀ ⦃x y : X⦄, x ⤳ y → (x ∈ S ↔ y ∈ S)) : IsClosed S := by
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  have : S = ⋃ C ∈ {C ∈ irreducibleComponents X | (C ∩ S).Nonempty}, C := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, y,
        mem_irreducibleComponent, hy⟩, mem_irreducibleComponent⟩
    · rintro ⟨C, ⟨hC, x, hxC, hxS⟩, hyC⟩
      obtain ⟨η, hη⟩ := QuasiSober.sober (hC.1 : IsIrreducible C)
        (isClosed_of_mem_irreducibleComponents C hC)
      exact (hS (hη.specializes hyC)).1 ((hS (hη.specializes hxC)).2 hxS)
  rw [this]
  exact (hfin.subset fun C hC ↦ hC.1).isClosed_biUnion fun C hC ↦
    isClosed_of_mem_irreducibleComponents C hC.1

end Topology

namespace AlgebraicGeometry

/-- On a locally Noetherian scheme, a function which is constant along specializations is
locally constant. -/
theorem isLocallyConstant_of_specializes {Y : Scheme.{u}} [IsLocallyNoetherian Y] {α : Type*}
    {f : Y → α} (hf : ∀ ⦃η y : Y⦄, η ⤳ y → f η = f y) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_exists_open f).2 fun y ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  have : QuasiSober V := V.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  let S : Set V := {v | f v.1 = f y}
  have hS : ∀ ⦃a b : V⦄, a ⤳ b → (a ∈ Sᶜ ↔ b ∈ Sᶜ) := fun a b h ↦ by
    have : f a.1 = f b.1 := hf (h.map continuous_subtype_val)
    exact not_congr (show f a.1 = f y ↔ f b.1 = f y by rw [this])
  have hSo : IsOpen S := isClosed_compl_iff.1 (NoetherianSpace.isClosed_of_specializes_iff hS)
  refine ⟨Subtype.val '' S, V.isOpen.isOpenMap_subtype_val _ hSo,
    ⟨⟨y, hyV⟩, (rfl : f y = f y), rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hv

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AdicSheaf

/-- **Kernels and cokernels of locally constant rank are lisse.** A morphism of finite free
`ℚ̄_ℓ,T`-modules whose matrix of functions has locally constant rank has lisse kernel and
cokernel: on the open subschemes where the rank is constant, this is
`AlgebraicGeometry.ProEtale.AdicSheaf.isAdicLisseSheaf_kernel_cokernel_of_rank_eq`. -/
theorem isAdicLisseSheaf_kernel_cokernel_of_isLocallyConstant {T : Scheme.{u}} {ι κ : Type}
    [Fintype ι] [Fintype κ] (ψ : (⨁ fun _ : ι ↦ unit l T) ⟶ ⨁ fun _ : κ ↦ unit l T)
    (hψ : IsLocallyConstant fun t : T ↦
      ((unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank) :
    IsAdicLisseSheaf (kernel ψ) ∧ IsAdicLisseSheaf (cokernel ψ) := by
  set rk := fun t : T ↦ ((unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank
  let O (t : T) : T.Opens := ⟨rk ⁻¹' {rk t}, hψ.isOpen_fiber _⟩
  have hR : Presieve.ofArrows (fun t ↦ (O t).toScheme) (fun t ↦ (O t).ι) ∈
      Scheme.proetalePrecoverage T :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).2
        ⟨fun x ↦ ⟨x, by simp [O]⟩, fun _ ↦ inferInstance⟩)
  have key (t : T) : IsAdicLisseSheaf (kernel (((O t).ι)^*ᵃ[l].map ψ)) ∧
      IsAdicLisseSheaf (cokernel (((O t).ι)^*ᵃ[l].map ψ)) := by
    refine isAdicLisseSheaf_kernel_of_eq_comp _ _ (freeUpperStarIso l ι (O t).ι).symm
      (freeUpperStarIso l κ (O t).ι) rfl
      (isAdicLisseSheaf_kernel_cokernel_of_rank_eq _ (rk t) fun w ↦ ?_)
    rw [Iso.symm_hom, unitMatrix_adicUpperStar]
    exact w.2
  exact ⟨IsAdicLisseSheaf.of_presieve _ hR fun _ _ ⟨t⟩ ↦
      (key t).1.of_iso (PreservesKernel.iso _ _).symm,
    IsAdicLisseSheaf.of_presieve _ hR fun _ _ ⟨t⟩ ↦
      (key t).2.of_iso (PreservesCokernel.iso _ _).symm⟩

end AdicSheaf

open AdicSheaf in
/-- **Kernels and cokernels of lisse sheaves are lisse** on a locally Noetherian scheme: the
pointwise rank of a morphism of lisse sheaves descends to a function on `Y` which is constant
along specializations, hence locally constant. -/
theorem IsAdicLisseSheaf.kernel_cokernel {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {F G : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G) (φ : F ⟶ G) :
    IsAdicLisseSheaf (kernel φ) ∧ IsAdicLisseSheaf (cokernel φ) := by
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
  let M (k : Σ _ : ι, ι') := unitMatrix ((eF k).inv ≫ (g k)^*ᵃ[l].map φ ≫ (eG k).hom)
  let rk (k : Σ _ : ι, ι') (v : W k) : ℕ :=
    ((M k).map (PadicAlgCl.locallyFiniteFunctionsEval v)).rank
  have hfc (k k' : Σ _ : ι, ι') (v : W k) (v' : W k') (h : g k v = g k' v') :
      rk k v = rk k' v' :=
    rank_eq_of_apply_eq φ (g k) (g k') (eF k) (eG k) (eF k') (eG k') v v' h
  have hspec (k : Σ _ : ι, ι') {v₀ v : W k} (hv : v₀ ⤳ v) : rk k v₀ = rk k v := by
    have : (M k).map (PadicAlgCl.locallyFiniteFunctionsEval v₀) =
        (M k).map (PadicAlgCl.locallyFiniteFunctionsEval v) := by
      ext a b
      exact (hv.map ((M k) a b).1.continuous).eq
    simp only [rk, this]
  have hsurj : ∀ y, ∃ k, y ∈ Set.range (g k) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hW)).1
  choose kk vv hvv using hsurj
  let Rk (y : Y) : ℕ := rk (kk y) (vv y)
  have hRk (k : Σ _ : ι, ι') (v : W k) : Rk (g k v) = rk k v :=
    hfc _ _ _ _ (hvv _)
  have hgen {η y : Y} (hηy : η ⤳ y) : Rk η = Rk y := by
    have hg : GeneralizingMap (g (kk y)) := Flat.generalizingMap _
    obtain ⟨v₀, hv₀, hfv₀⟩ := hg (show η ⤳ (g (kk y)) (vv y) by rw [hvv]; exact hηy)
    rw [← hfv₀, hRk]
    exact hspec _ hv₀
  have hlc : IsLocallyConstant Rk := isLocallyConstant_of_specializes fun _ _ h ↦ hgen h
  have hmem (k : Σ _ : ι, ι') : IsAdicLisseSheaf (kernel ((g k)^*ᵃ[l].map φ)) ∧
      IsAdicLisseSheaf (cokernel ((g k)^*ᵃ[l].map φ)) := by
    refine isAdicLisseSheaf_kernel_of_eq_comp _ _ (eF k).symm (eG k) rfl
      (isAdicLisseSheaf_kernel_cokernel_of_isLocallyConstant _ ?_)
    have : rk k = Rk ∘ (g k).base := funext fun v ↦ (hRk k v).symm
    have h := hlc.comp_continuous (g k).base.hom.continuous
    rw [← this] at h
    exact h
  exact ⟨IsAdicLisseSheaf.of_presieve _ hW fun _ _ ⟨k⟩ ↦
      (hmem k).1.of_iso (PreservesKernel.iso _ _).symm,
    IsAdicLisseSheaf.of_presieve _ hW fun _ _ ⟨k⟩ ↦
      (hmem k).2.of_iso (PreservesCokernel.iso _ _).symm⟩

/-- A sheaf which becomes free of positive rank on a weakly étale `f : V ⟶ Y` has nonzero stalks
at the geometric points of `Y` lifting to `V`: the stalk contains `Γ(Spec K, ℚ̄_ℓ) ≠ 0` as a
direct summand. -/
lemma nontrivial_globalSections_upperStar_of_iso {Y V : Scheme.{u}} {H : AdicSheaf l Y}
    (f : V ⟶ Y) [WeaklyEtale f] {n : ℕ}
    (e : (f)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V) (hn : 0 < n)
    {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Y)
    (hs : s.base (IsLocalRing.closedPoint K) ∈ Set.range f.base) :
    Nontrivial ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((s)^*[_].obj H.X)) := by
  obtain ⟨t, ht⟩ := exists_comp_eq_of_weaklyEtale f s hs
  let E : (s)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K)) :=
    (adicUpperStarCongr l ht.symm).app H ≪≫ AdicSheaf.trivPull f e t
  let a := biproduct.ι (fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K))) ⟨0, hn⟩ ≫ E.inv
  let b := E.hom ≫ biproduct.π (fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K))) ⟨0, hn⟩
  have hab : a.hom ≫ b.hom = 𝟙 _ := by
    rw [← Mod.comp_hom']
    simp [a, b]
  have : Nonempty (Spec (.of K)) := ⟨IsLocalRing.closedPoint K⟩
  have : Nontrivial ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      (AdicSheaf.unit l (Spec (.of K))).X) :=
    nontrivial_globalSections_adicConstantSheaf (l := l) (Spec (.of K))
  refine Function.Injective.nontrivial (f := ((Sheaf.Γ _ _).map a.hom).hom) fun x x' hxx' ↦ ?_
  have h₁ := congrArg ((Sheaf.Γ _ _).map b.hom).hom hxx'
  have h₂ (z) : ((Sheaf.Γ _ _).map b.hom).hom (((Sheaf.Γ _ _).map a.hom).hom z) = z := by
    have := congrArg (fun φ ↦ φ.hom z) (((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K)))
      (WeilCoefficients.{u} l)).map_comp a.hom b.hom).symm.trans
        ((congrArg (Sheaf.Γ _ _).map hab).trans ((Sheaf.Γ _ _).map_id _)))
    simpa using this
  rwa [h₂, h₂] at h₁

/-- **A lisse sheaf with enough vanishing stalks vanishes.** Let `H` be a lisse sheaf on `Y`
such that every point `y` of `Y` is a specialization of a point `η` which also specializes to
the image of a geometric point `s` at which the stalk of `H` vanishes. Then `H = 0`: the rank of
a trivialisation of `H` descends to `Y`, is constant along specializations (flat morphisms lift
generizations), and is positive at the image of `s` if it is positive anywhere above `y`. -/
theorem IsAdicLisseSheaf.isZero_of_subsingleton_globalSections_upperStar {Y : Scheme.{u}}
    {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) (K : Type u) [Field K] [IsAlgClosed K]
    (h : ∀ y : Y, ∃ (η : Y) (s : Spec (.of K) ⟶ Y), η ⤳ y ∧
      η ⤳ s.base (IsLocalRing.closedPoint K) ∧
      Subsingleton ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((s)^*[_].obj H.X))) :
    IsZero H := by
  classical
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  have hn (i i' : ι) (v : V i) (v' : V i') (hvv' : f i v = f i' v') : n i = n i' := by
    have := AdicSheaf.rank_eq_of_apply_eq (𝟙 H) (f i) (f i') (e i).some (e i).some (e i').some
      (e i').some v v' hvv'
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id, AdicSheaf.unitMatrix_id, AdicSheaf.unitMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.rank_one, Matrix.rank_one, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  have hsurj : ∀ y, ∃ j, y ∈ Set.range (f j) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hR)).1
  have hz (i : ι) : IsZero ((f i)^*ᵃ[l].obj H) := by
    by_cases hV : Nonempty (V i)
    · obtain ⟨v⟩ := hV
      suffices h0 : n i = 0 by
        refine IsZero.of_iso ?_ (e i).some
        rw [h0]
        exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
          fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩
      by_contra hpos
      obtain ⟨η, s, hη, hηs, hsub⟩ := h (f i v)
      obtain ⟨v₀, -, hv₀⟩ := Flat.generalizingMap (f i) hη
      obtain ⟨j, w, hw⟩ := hsurj (s.base (IsLocalRing.closedPoint K))
      obtain ⟨w₀, -, hw₀⟩ := Flat.generalizingMap (f j) (show η ⤳ f j w by rw [hw]; exact hηs)
      have hnj : 0 < n j := (hn j i w₀ v₀ (hw₀.trans hv₀.symm)) ▸ Nat.pos_of_ne_zero hpos
      have := nontrivial_globalSections_upperStar_of_iso (f j) (e j).some hnj s ⟨w, hw⟩
      exact not_subsingleton _ hsub
    · have : IsEmpty (V i) := not_nonempty_iff.1 hV
      exact isZero_adicSheaf_of_isEmpty l _
  have : IsIso (0 : H ⟶ 0) := isIso_of_isIso_adicUpperStar l f hR _ fun i ↦ by
    have hz' : IsZero ((f i)^*ᵃ[l].obj 0) := Functor.map_isZero _ (isZero_zero _)
    rw [(hz i).eq_of_src ((f i)^*ᵃ[l].map 0) ((hz i).iso hz').hom]
    infer_instance
  exact (isZero_zero _).of_iso (asIso (0 : H ⟶ 0))

end ProEtale

end AlgebraicGeometry
