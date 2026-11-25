/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk

/-!
# Lisse `ℓ`-adic sheaves on an irreducible scheme

On an irreducible scheme `Y` the pointwise rank of a morphism of lisse sheaves is constant: it
descends to `Y` along a trivialising pro-étale cover
(`AlgebraicGeometry.ProEtale.AdicSheaf.rank_eq_of_apply_eq`), is constant along specializations
(the entries of the matrices are continuous functions to the Hausdorff space `ℚ̄_ℓ`, and flat
morphisms lift generizations), and every point of `Y` is a specialization of the generic point.
Hence kernels and cokernels of morphisms of lisse sheaves are lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.kernel_cokernel_of_irreducibleSpace`): the lisse
sheaves on `Y` form an abelian subcategory.

Likewise a lisse sheaf `H` on `Y` has a rank `r`: its pullback to every geometric point is
`ℚ̄_ℓ^r`, and `H = 0` if and only if `r = 0`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_rank_of_irreducibleSpace`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

open AdicSheaf in
/-- **Kernels and cokernels of lisse sheaves on an irreducible scheme are lisse.** The pointwise
rank of a morphism of lisse sheaves descends to `Y`, is constant along specializations, hence
equal everywhere to its value at the generic point; morphisms of finite free modules of constant
rank have lisse kernel and cokernel. -/
theorem IsAdicLisseSheaf.kernel_cokernel_of_irreducibleSpace [IrreducibleSpace Y]
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
  -- every point of a member generizes to a point over the generic point of `Y`
  have hgen (k k' : Σ _ : ι, ι') (v : W k) (v' : W k') : rk k v = rk k' v' := by
    obtain ⟨v₀, hv₀, h₀⟩ := Flat.generalizingMap (g k) (genericPoint_specializes (g k v))
    obtain ⟨v₀', hv₀', h₀'⟩ := Flat.generalizingMap (g k') (genericPoint_specializes (g k' v'))
    rw [← hspec k hv₀, ← hspec k' hv₀']
    exact hfc _ _ _ _ (h₀.trans h₀'.symm)
  have hmem (k : Σ _ : ι, ι') : IsAdicLisseSheaf (kernel ((g k)^*ᵃ[l].map φ)) ∧
      IsAdicLisseSheaf (cokernel ((g k)^*ᵃ[l].map φ)) := by
    refine isAdicLisseSheaf_kernel_of_eq_comp _ _ (eF k).symm (eG k) rfl ?_
    by_cases hk : Nonempty (W k)
    · obtain ⟨w₀⟩ := hk
      exact isAdicLisseSheaf_kernel_cokernel_of_rank_eq _ (rk k w₀) fun w ↦ hgen k k w w₀
    · exact isAdicLisseSheaf_kernel_cokernel_of_rank_eq _ 0 fun w ↦ (hk ⟨w⟩).elim
  exact ⟨IsAdicLisseSheaf.of_presieve _ hW fun _ _ ⟨k⟩ ↦
      (hmem k).1.of_iso (PreservesKernel.iso _ _).symm,
    IsAdicLisseSheaf.of_presieve _ hW fun _ _ ⟨k⟩ ↦
      (hmem k).2.of_iso (PreservesCokernel.iso _ _).symm⟩

open ZeroObject in
/-- **The rank of a lisse sheaf on an irreducible scheme.** A lisse sheaf `H` on an irreducible
scheme `Y` has a rank `r`: its pullback to every geometric point `s : Spec K ⟶ Y` is `ℚ̄_ℓ^r`,
and `H = 0` if and only if `r = 0`. The rank of a trivialisation descends to `Y`, and any two
members of a trivialising cover have points over the generic point of `Y`, flat morphisms lifting
generizations. -/
theorem IsAdicLisseSheaf.exists_rank_of_irreducibleSpace [IrreducibleSpace Y]
    {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) :
    ∃ r : ℕ, (IsZero H ↔ r = 0) ∧ ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (.of K) ⟶ Y), Nonempty ((s)^*ᵃ[l].obj H ≅
        ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of K))) := by
  classical
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  -- the rank of the trivialisations descends to `Y`
  have hn (i i' : ι) (v : V i) (v' : V i') (hvv' : f i v = f i' v') : n i = n i' := by
    have := AdicSheaf.rank_eq_of_apply_eq (𝟙 H) (f i) (f i') (e i).some (e i).some (e i').some
      (e i').some v v' hvv'
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id, AdicSheaf.unitMatrix_id, AdicSheaf.unitMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.rank_one, Matrix.rank_one, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  -- every member with a point has a point over the generic point
  have hgen (i i' : ι) (v : V i) (v' : V i') : n i = n i' := by
    obtain ⟨v₀, -, h₀⟩ := Flat.generalizingMap (f i) (genericPoint_specializes (f i v))
    obtain ⟨v₀', -, h₀'⟩ := Flat.generalizingMap (f i') (genericPoint_specializes (f i' v'))
    exact hn _ _ _ _ (h₀.trans h₀'.symm)
  have hsurj : ∀ y, ∃ i, y ∈ Set.range (f i) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hR)).1
  obtain ⟨i₀, v₀, -⟩ := hsurj (genericPoint Y)
  refine ⟨n i₀, ⟨fun hz ↦ ?_, fun h0 ↦ ?_⟩, fun K _ _ s ↦ ?_⟩
  · by_contra hne
    have hz' : IsZero (⨁ fun _ : Fin (n i₀) ↦ AdicSheaf.unit l (V i₀)) :=
      (Functor.map_isZero _ hz).of_iso (e i₀).some.symm
    have : Nonempty (V i₀) := ⟨v₀⟩
    exact not_isZero_adicConstantSheaf l (V i₀) ((AdicSheaf.forget _).map_isZero
      (IsZero.of_mono (biproduct.ι (fun _ : Fin (n i₀) ↦ AdicSheaf.unit l (V i₀))
        ⟨0, Nat.pos_of_ne_zero hne⟩) hz'))
  · have hz (i : ι) : IsZero ((f i)^*ᵃ[l].obj H) := by
      by_cases hV : Nonempty (V i)
      · obtain ⟨v⟩ := hV
        refine IsZero.of_iso ?_ (e i).some
        rw [hgen i i₀ v v₀, h0]
        exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
          fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩
      · have : IsEmpty (V i) := not_nonempty_iff.1 hV
        exact isZero_adicSheaf_of_isEmpty l _
    have : IsIso (0 : H ⟶ 0) := isIso_of_isIso_adicUpperStar l f hR _ fun i ↦ by
      have hz' : IsZero ((f i)^*ᵃ[l].obj 0) := Functor.map_isZero _ (isZero_zero _)
      rw [(hz i).eq_of_src ((f i)^*ᵃ[l].map 0) ((hz i).iso hz').hom]
      infer_instance
    exact (isZero_zero _).of_iso (asIso (0 : H ⟶ 0))
  · obtain ⟨j, w, hw⟩ := hsurj (s.base (IsLocalRing.closedPoint K))
    obtain ⟨t, ht⟩ := exists_comp_eq_of_weaklyEtale (f j) s ⟨w, hw⟩
    rw [← hgen j i₀ w v₀]
    exact ⟨(adicUpperStarCongr l ht.symm).app H ≪≫ AdicSheaf.trivPull (f j) (e j).some t⟩

section Stalk

variable {K : Type u} [Field K] [IsAlgClosed K]

variable (l) in
/-- The stalk `Γ(Spec K, s^* H)` of an `ℓ`-adic sheaf at a geometric point `s : Spec K ⟶ Y`, as
a `ℚ̄_ℓ`-vector space. -/
noncomputable abbrev geometricStalkFunctor (s : Spec (.of K) ⟶ Y) :
    AdicSheaf l Y ⥤ WeilCoefficients.{u} l :=
  (s)^*ᵃ[l] ⋙ AdicSheaf.forget _ ⋙ Sheaf.Γ _ _

instance (s : Spec (.of K) ⟶ Y) : (geometricStalkFunctor l s).PreservesMonomorphisms := by
  unfold geometricStalkFunctor
  infer_instance

/-- The geometric stalk functor is exact on the right: the global sections on the spectrum of an
algebraically closed field preserve epimorphisms. -/
instance (s : Spec (.of K) ⟶ Y) : (geometricStalkFunctor l s).PreservesEpimorphisms := by
  have : ((s)^*ᵃ[l]).PreservesEpimorphisms := inferInstance
  have : (AdicSheaf.forget (l := l) (Spec (.of K))).PreservesEpimorphisms := inferInstance
  have := preservesEpimorphisms_Γ_of_isAlgClosed (K := K) (l := l)
  exact @Functor.preservesEpimorphisms_comp _ _ _ _ _ _ _ _ ‹_›
    (@Functor.preservesEpimorphisms_comp _ _ _ _ _ _ _ _ ‹_›
      ‹_›)

omit [IsAlgClosed K] in
/-- The stalk of `ℚ̄_ℓ^r` at a geometric point has dimension `r`. -/
lemma finrank_geometricStalkFunctor_of_iso (s : Spec (.of K) ⟶ Y) {H : AdicSheaf l Y} {r : ℕ}
    (e : (s)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of K))) :
    Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj H)) = r := by
  rw [← finrank_globalSections_biproduct_unit (l := l) K r]
  exact ((AdicSheaf.forget _ ⋙ Sheaf.Γ _ _ ⋙ WeilCoefficients.toModuleCat l).mapIso
    e).toLinearEquiv.finrank_eq

omit [IsAlgClosed K] in
/-- The stalk of the constant sheaf `ℚ̄_ℓ` at a geometric point is a line. -/
theorem finrank_geometricStalkFunctor_unit (s : Spec (.of K) ⟶ Y) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((geometricStalkFunctor l s).obj (AdicSheaf.unit l Y))) = 1 :=
  finrank_geometricStalkFunctor_of_iso s
    (adicUpperStarUnitIso l s ≪≫ (biproductUniqueIso (fun _ : Fin 1 ↦ _)).symm)

variable [IrreducibleSpace Y] {H : AdicSheaf l Y}

/-- On an irreducible scheme the stalks of a lisse sheaf at all geometric points have the same
dimension, the rank. -/
theorem IsAdicLisseSheaf.finrank_geometricStalkFunctor_eq (hH : IsAdicLisseSheaf H)
    (s : Spec (.of K) ⟶ Y) {K' : Type u} [Field K'] [IsAlgClosed K'] (s' : Spec (.of K') ⟶ Y) :
    Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj H)) =
    Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s').obj H)) := by
  obtain ⟨r, -, hr⟩ := hH.exists_rank_of_irreducibleSpace
  rw [finrank_geometricStalkFunctor_of_iso s (hr K s).some,
    finrank_geometricStalkFunctor_of_iso s' (hr K' s').some]

/-- On an irreducible scheme a lisse sheaf vanishes if and only if its stalk at one geometric
point does. -/
theorem IsAdicLisseSheaf.isZero_iff_finrank_geometricStalkFunctor_eq_zero
    (hH : IsAdicLisseSheaf H) (s : Spec (.of K) ⟶ Y) :
    IsZero H ↔ Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj H)) = 0 := by
  obtain ⟨r, hr0, hr⟩ := hH.exists_rank_of_irreducibleSpace
  rw [finrank_geometricStalkFunctor_of_iso s (hr K s).some, hr0]

/-- The stalks of a lisse sheaf on an irreducible scheme are finite-dimensional. -/
theorem IsAdicLisseSheaf.finiteDimensional_geometricStalkFunctor (hH : IsAdicLisseSheaf H)
    (s : Spec (.of K) ⟶ Y) : FiniteDimensional (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj H)) := by
  by_cases h : IsZero H
  · have : Subsingleton ((WeilCoefficients.toModuleCat l).obj
        ((geometricStalkFunctor l s).obj H)) :=
      ModuleCat.subsingleton_of_isZero (Functor.map_isZero _ (Functor.map_isZero _ h))
    infer_instance
  · exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero fun h0 ↦
      h ((hH.isZero_iff_finrank_geometricStalkFunctor_eq_zero s).2 h0))

/-- A monomorphism into a lisse sheaf on an irreducible scheme does not increase the stalk
dimension. -/
theorem finrank_geometricStalkFunctor_le_of_mono {A X : AdicSheaf l Y} (hX : IsAdicLisseSheaf X)
    (i : A ⟶ X) [Mono i] (s : Spec (.of K) ⟶ Y) :
    Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj A)) ≤
    Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj X)) := by
  have := hX.finiteDimensional_geometricStalkFunctor s
  exact LinearMap.finrank_le_finrank_of_injective
    (f := ((WeilCoefficients.toModuleCat l).map ((geometricStalkFunctor l s).map i)).hom)
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- **A monomorphism of lisse sheaves of the same rank is an isomorphism**, on an irreducible
scheme: its cokernel is lisse, with zero stalk. -/
theorem IsAdicLisseSheaf.isIso_of_mono_of_finrank_eq {A X : AdicSheaf l Y}
    (hA : IsAdicLisseSheaf A) (hX : IsAdicLisseSheaf X) (i : A ⟶ X) [Mono i]
    (s : Spec (.of K) ⟶ Y)
    (h : Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj A)) =
    Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj X))) :
    IsIso i := by
  have := hA.finiteDimensional_geometricStalkFunctor s
  have := hX.finiteDimensional_geometricStalkFunctor s
  have hC := (hA.kernel_cokernel_of_irreducibleSpace hX i).2
  let ω := geometricStalkFunctor l s
  have hsurj : Function.Surjective
      ((WeilCoefficients.toModuleCat l).map (ω.map i)).hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).1
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have hπ : Function.Surjective (ω.map (cokernel.π i)).hom :=
    (ModuleCat.epi_iff_surjective _).1 (Functor.map_epi ω (cokernel.π i))
  have hzero : ω.map i ≫ ω.map (cokernel.π i) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have : Subsingleton ((WeilCoefficients.toModuleCat l).obj (ω.obj (cokernel i))) := by
    refine ⟨fun y y' ↦ ?_⟩
    have key (z : (WeilCoefficients.toModuleCat l).obj (ω.obj (cokernel i))) : z = 0 := by
      obtain ⟨x, rfl⟩ := hπ z
      obtain ⟨a, rfl⟩ := hsurj x
      exact congrArg (fun φ ↦ φ.hom a) hzero
    rw [key y, key y']
  have hz := (hC.isZero_iff_finrank_geometricStalkFunctor_eq_zero s).2
    Module.finrank_zero_of_subsingleton
  have : Epi i := Abelian.epi_of_cokernel_π_eq_zero _ (hz.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi i

end Stalk

section Irreducible

variable [IrreducibleSpace Y]

/-- The image of a morphism of lisse sheaves on an irreducible scheme is lisse: it is the
kernel of the cokernel. -/
theorem IsAdicLisseSheaf.image {A X : AdicSheaf l Y} (hA : IsAdicLisseSheaf A)
    (hX : IsAdicLisseSheaf X) (f : A ⟶ X) : IsAdicLisseSheaf (Limits.image f) :=
  (hX.kernel_cokernel_of_irreducibleSpace (hA.kernel_cokernel_of_irreducibleSpace hX f).2
    (cokernel.π f)).1.of_iso (Abelian.imageIsoImage f)

omit [IrreducibleSpace Y] in
/-- A monomorphism from a nonzero lisse sheaf to an irreducible local system is an
isomorphism. -/
theorem IsIrreducibleAdicLocalSystem.isIso_of_mono {S A : AdicSheaf l Y}
    (hS : IsIrreducibleAdicLocalSystem S) (hA : IsAdicLisseSheaf A) (hA0 : ¬ IsZero A)
    (j : A ⟶ S) [Mono j] : IsIso j :=
  (hS.2.2 A j inferInstance hA).resolve_left hA0

/-- **Schur's lemma for irreducible local systems.** On an irreducible scheme, a nonzero
morphism between irreducible local systems is an isomorphism: its kernel is a lisse subsheaf,
hence zero, and a monomorphism into an irreducible local system is an isomorphism. -/
theorem IsIrreducibleAdicLocalSystem.isIso_of_ne_zero {S T : AdicSheaf l Y}
    (hS : IsIrreducibleAdicLocalSystem S) (hT : IsIrreducibleAdicLocalSystem T) (g : S ⟶ T)
    (hg : g ≠ 0) : IsIso g := by
  have hK := (hS.1.kernel_cokernel_of_irreducibleSpace hT.1 g).1
  rcases hS.2.2 _ (kernel.ι g) inferInstance hK with h | h
  · have : Mono g := Preadditive.mono_of_isZero_kernel g h
    exact hT.isIso_of_mono hS.1 hS.2.1 g
  · exact (hg (by rw [← cancel_epi (kernel.ι g), kernel.condition, comp_zero])).elim

/-- **A nonzero lisse sheaf on an irreducible scheme contains an irreducible local system**: a
nonzero lisse subsheaf of minimal rank. -/
theorem IsAdicLisseSheaf.exists_mono_isIrreducibleAdicLocalSystem {H : AdicSheaf l Y}
    (hH : IsAdicLisseSheaf H) (hH0 : ¬ IsZero H) :
    ∃ (S : AdicSheaf l Y) (j : S ⟶ H), Mono j ∧ IsIrreducibleAdicLocalSystem S := by
  classical
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y
  let d (A : AdicSheaf l Y) : ℕ := Module.finrank (PadicAlgCl l)
    ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj A))
  let P (n : ℕ) : Prop := ∃ (S : AdicSheaf l Y) (j : S ⟶ H), Mono j ∧ IsAdicLisseSheaf S ∧
    ¬ IsZero S ∧ d S = n
  have hP : ∃ n, P n := ⟨d H, H, 𝟙 H, inferInstance, hH, hH0, rfl⟩
  obtain ⟨S, j, hj, hS, hS0, hd⟩ := Nat.find_spec hP
  refine ⟨S, j, hj, hS, hS0, fun A j' _ hA ↦ ?_⟩
  by_cases hA0 : IsZero A
  · exact Or.inl hA0
  · refine Or.inr (hA.isIso_of_mono_of_finrank_eq hS j' s (le_antisymm
      (finrank_geometricStalkFunctor_le_of_mono hS j' s) ?_))
    change d S ≤ d A
    rw [hd]
    exact Nat.find_min' hP ⟨A, j' ≫ j, inferInstance, hA, hA0, rfl⟩

omit [IrreducibleSpace Y] in
/-- Being an irreducible local system is invariant under isomorphism. -/
theorem IsIrreducibleAdicLocalSystem.of_iso {S T : AdicSheaf l Y} (e : S ≅ T)
    (hS : IsIrreducibleAdicLocalSystem S) : IsIrreducibleAdicLocalSystem T := by
  refine ⟨hS.1.of_iso e, fun h ↦ hS.2.1 (h.of_iso e), fun A j _ hA ↦ ?_⟩
  rcases hS.2.2 A (j ≫ e.inv) inferInstance hA with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using IsIso.comp_isIso' h (inferInstance : IsIso e.hom))

omit [IrreducibleSpace Y] in
/-- A biproduct over `Fin 0` vanishes. -/
lemma isZero_biproduct_fin_zero (S : Fin 0 → AdicSheaf l Y) : IsZero (⨁ S) :=
  ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
    fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩

omit [IrreducibleSpace Y] in
/-- The biproduct over `Fin (n + 1)` splits off its last summand. -/
lemma nonempty_iso_biproduct_fin_succ {n : ℕ} (S : Fin (n + 1) → AdicSheaf l Y) :
    Nonempty (⨁ S ≅ (⨁ fun i : Fin n ↦ S i.castSucc) ⊞ S (Fin.last n)) :=
  ⟨(biproduct.whiskerEquiv (f := fun t : Fin n ⊕ Fin 1 ↦ S (finSumFinEquiv t)) (g := S)
      finSumFinEquiv (fun _ ↦ Iso.refl _)).symm ≪≫
    (biprodBiproductSumIso (fun t : Fin n ⊕ Fin 1 ↦ S (finSumFinEquiv t))).symm ≪≫
    biprod.mapIso (Iso.refl _) (biproductUniqueIso _)⟩

omit [IrreducibleSpace Y] in
/-- A finite direct sum of lisse sheaves is lisse. -/
theorem IsAdicLisseSheaf.biproduct_fin :
    ∀ (n : ℕ) (S : Fin n → AdicSheaf l Y), (∀ i, IsAdicLisseSheaf (S i)) → IsAdicLisseSheaf (⨁ S)
  | 0, S, _ => .of_isZero (isZero_biproduct_fin_zero S)
  | n + 1, S, h => ((IsAdicLisseSheaf.biproduct_fin n _ fun i ↦ h i.castSucc).biprod
      (h (Fin.last n))).of_iso (nonempty_iso_biproduct_fin_succ S).some.symm

/-- **A constituent of a sum of irreducible local systems is one of the summands.** On an
irreducible scheme, if an irreducible local system `Q` is a quotient of a lisse subsheaf `E` of
`S₀ ⊕ ⋯ ⊕ S_{n-1}`, with the `Sᵢ` irreducible local systems, then some `Sᵢ` has a nonzero
morphism to `Q`. Either the part of `E` in the first summands already surjects onto `Q`, or `Q`
is a quotient of the image of `E` in the last summand, which is all of it. -/
theorem IsIrreducibleAdicLocalSystem.exists_ne_zero_of_mono_of_epi {Q : AdicSheaf l Y}
    (hQ : IsIrreducibleAdicLocalSystem Q) (n : ℕ) :
    ∀ (S : Fin n → AdicSheaf l Y) (_ : ∀ i, IsIrreducibleAdicLocalSystem (S i))
      (E : AdicSheaf l Y) (_ : IsAdicLisseSheaf E) (j : E ⟶ ⨁ S) (q : E ⟶ Q) [Mono j] [Epi q],
      ∃ i, ∃ g : S i ⟶ Q, g ≠ 0 := by
  induction n with
  | zero =>
    intro S _ E _ j q _ _
    exact (hQ.2.1 (IsZero.of_epi q (IsZero.of_mono j (isZero_biproduct_fin_zero S)))).elim
  | succ n ih =>
    intro S hS E hE j q _ _
    have hq : q ≠ 0 := fun h ↦ hQ.2.1 (IsZero.of_epi_eq_zero q h)
    obtain ⟨e⟩ := nonempty_iso_biproduct_fin_succ S
    let r : E ⟶ S (Fin.last n) := j ≫ e.hom ≫ biprod.snd
    have hK := (hE.kernel_cokernel_of_irreducibleSpace (hS _).1 r).1
    by_cases hk : kernel.ι r ≫ q = 0
    · -- `q` factors through the coimage of `r`, which is all of the last summand
      let q' : Abelian.coimage r ⟶ Q := cokernel.desc _ q hk
      let m : Abelian.coimage r ⟶ S (Fin.last n) :=
        Abelian.coimageImageComparison r ≫ Abelian.image.ι r
      have hC : IsAdicLisseSheaf (Abelian.coimage r) :=
        (hK.kernel_cokernel_of_irreducibleSpace hE (kernel.ι r)).2
      have hq' : q = Abelian.coimage.π r ≫ q' := (cokernel.π_desc _ _ _).symm
      have hC0 : ¬ IsZero (Abelian.coimage r) := fun h ↦ hq (by rw [hq', h.eq_of_src q', comp_zero])
      have := (hS (Fin.last n)).isIso_of_mono hC hC0 m
      refine ⟨Fin.last n, inv m ≫ q', fun hg ↦ hq ?_⟩
      rw [hq', ← IsIso.hom_inv_id_assoc m q', hg, comp_zero, comp_zero]
    · -- the part of `E` in the first summands surjects onto `Q`
      have hI : IsIso (image.ι (kernel.ι r ≫ q)) :=
        hQ.isIso_of_mono (hK.image hQ.1 _)
          (fun h ↦ hk (by rw [← image.fac (kernel.ι r ≫ q), h.eq_of_tgt (factorThruImage _) 0,
            zero_comp])) _
      have : Epi (kernel.ι r ≫ q) := by
        rw [← image.fac (kernel.ι r ≫ q)]
        infer_instance
      let j₁ := kernel.ι r ≫ j ≫ e.hom ≫ biprod.fst
      have hj₁ : kernel.ι r ≫ j ≫ e.hom = j₁ ≫ biprod.inl := by
        apply biprod.hom_ext
        · simp [j₁]
        · simp only [Category.assoc, biprod.inl_snd, comp_zero]
          exact kernel.condition r
      have : Mono (kernel.ι r ≫ j ≫ e.hom) := inferInstance
      rw [hj₁] at this
      have : Mono j₁ := mono_of_mono j₁ (biprod.inl (Y := S (Fin.last n)))
      obtain ⟨i, g, hg⟩ := ih (fun i ↦ S i.castSucc) (fun i ↦ hS _) (kernel r) hK j₁
        (kernel.ι r ≫ q)
      exact ⟨i.castSucc, g, hg⟩

/-- On an irreducible scheme the constant sheaf `ℚ̄_ℓ` is an irreducible local system: a lisse
subsheaf has rank at most one. -/
theorem isIrreducibleAdicLocalSystem_unit :
    IsIrreducibleAdicLocalSystem (AdicSheaf.unit l Y) := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y
  refine ⟨isAdicLisseSheaf_adicConstantSheaf Y, fun h ↦
    not_isZero_adicConstantSheaf l Y ((AdicSheaf.forget _).map_isZero h), fun A j _ hA ↦ ?_⟩
  have hle := finrank_geometricStalkFunctor_le_of_mono (isAdicLisseSheaf_adicConstantSheaf Y) j s
  rw [finrank_geometricStalkFunctor_unit] at hle
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
  · exact Or.inl ((hA.isZero_iff_finrank_geometricStalkFunctor_eq_zero s).2 h)
  · exact Or.inr (hA.isIso_of_mono_of_finrank_eq (isAdicLisseSheaf_adicConstantSheaf Y) j s
      (h.trans (finrank_geometricStalkFunctor_unit s).symm))

/-- **A lisse quotient of a finite sum of copies of `ℚ̄_ℓ` is a finite sum of copies of `ℚ̄_ℓ`**,
on an irreducible scheme. The image of the first summands is such a sum by induction, and the
remaining quotient is a quotient of the irreducible `ℚ̄_ℓ`, so it is zero or `ℚ̄_ℓ`, in which case
the extension splits. -/
theorem exists_iso_biproduct_unit_of_epi (n : ℕ) :
    ∀ (S : Fin n → AdicSheaf l Y) (_ : ∀ i, Nonempty (S i ≅ AdicSheaf.unit l Y))
      (X : AdicSheaf l Y) (_ : IsAdicLisseSheaf X) (π : ⨁ S ⟶ X) [Epi π],
      ∃ r : ℕ, Nonempty (X ≅ ⨁ fun _ : Fin r ↦ AdicSheaf.unit l Y) := by
  have hU : IsIrreducibleAdicLocalSystem (AdicSheaf.unit l Y) := isIrreducibleAdicLocalSystem_unit
  induction n with
  | zero =>
    intro S _ X _ π _
    exact ⟨0, ⟨(IsZero.of_epi π (isZero_biproduct_fin_zero S)).iso
      (isZero_biproduct_fin_zero _)⟩⟩
  | succ n ih =>
    intro S hS X hX π _
    obtain ⟨e⟩ := nonempty_iso_biproduct_fin_succ S
    have hW : IsAdicLisseSheaf (⨁ fun i : Fin n ↦ S i.castSucc) :=
      (IsAdicLisseSheaf.biproduct_const (isAdicLisseSheaf_adicConstantSheaf (l := l) Y) n).of_iso
        (biproduct.mapIso fun i ↦ (hS i.castSucc).some.symm)
    let π₁ := biprod.inl ≫ e.inv ≫ π
    have hX₁ : IsAdicLisseSheaf (Limits.image π₁) := hW.image hX π₁
    obtain ⟨r, ⟨e₁⟩⟩ := ih (fun i ↦ S i.castSucc) (fun i ↦ hS _) _ hX₁ (factorThruImage π₁)
    let ι₁ := image.ι π₁
    have hC := (hX₁.kernel_cokernel_of_irreducibleSpace hX ι₁).2
    let c : S (Fin.last n) ⟶ cokernel ι₁ := biprod.inr ≫ e.inv ≫ π ≫ cokernel.π ι₁
    have hfac : e.inv ≫ π ≫ cokernel.π ι₁ = biprod.snd ≫ c := by
      apply biprod.hom_ext'
      · simp only [biprod.inl_snd_assoc, zero_comp]
        change π₁ ≫ cokernel.π ι₁ = 0
        rw [← image.fac_assoc π₁, cokernel.condition, comp_zero]
      · simp [c]
    have : Epi (e.inv ≫ π ≫ cokernel.π ι₁) := inferInstance
    rw [hfac] at this
    have : Epi c := epi_of_epi (biprod.snd (X := ⨁ fun i : Fin n ↦ S i.castSucc)) c
    have hL := hU.of_iso (hS (Fin.last n)).some.symm
    by_cases hc : c = 0
    · have : Epi ι₁ := Abelian.epi_of_cokernel_π_eq_zero _
        ((IsZero.of_epi_eq_zero c hc).eq_of_tgt _ _)
      have : IsIso ι₁ := isIso_of_mono_of_epi ι₁
      exact ⟨r, ⟨(asIso ι₁).symm ≪≫ e₁⟩⟩
    · have : IsIso c := by
        rcases hL.2.2 _ (kernel.ι c) inferInstance
          (hL.1.kernel_cokernel_of_irreducibleSpace hC c).1 with h | h
        · have : Mono c := Preadditive.mono_of_isZero_kernel c h
          exact isIso_of_mono_of_epi c
        · exact (hc (by rw [← cancel_epi (kernel.ι c), kernel.condition, comp_zero])).elim
      let s : cokernel ι₁ ⟶ X := inv c ≫ biprod.inr ≫ e.inv ≫ π
      have hs : s ≫ cokernel.π ι₁ = 𝟙 _ := by
        simp only [s, Category.assoc]
        exact IsIso.inv_hom_id c
      let T := ShortComplex.mk ι₁ (cokernel.π ι₁) (cokernel.condition ι₁)
      have hT : T.Exact := T.exact_of_g_is_cokernel (cokernelIsCokernel ι₁)
      let sp := ShortComplex.Splitting.ofExactOfSection T hT s hs (inferInstance : Mono ι₁)
      let U := AdicSheaf.unit l Y
      exact ⟨r + 1, ⟨sp.isoBinaryBiproduct ≪≫
        biprod.mapIso e₁ ((asIso c).symm ≪≫ (hS (Fin.last n)).some ≪≫
          (biproductUniqueIso (fun _ : Fin 1 ↦ U)).symm) ≪≫
        biprodBiproductSumIso (fun _ : Fin r ⊕ Fin 1 ↦ U) ≪≫
        biproduct.whiskerEquiv (f := fun _ : Fin r ⊕ Fin 1 ↦ U) (g := fun _ : Fin (r + 1) ↦ U)
          finSumFinEquiv (fun _ ↦ Iso.refl _)⟩⟩

end Irreducible

end AlgebraicGeometry.ProEtale
