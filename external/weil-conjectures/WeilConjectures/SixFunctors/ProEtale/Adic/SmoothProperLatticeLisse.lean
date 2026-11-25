/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SmoothProperAdicLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleComparisonLocal
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntIsogenyLisse
public import WeilConjectures.NumberTheory.Padics.ULiftDiscreteValuationRing
public import WeilConjectures.NumberTheory.Padics.ULiftAdicComplete

/-!
# Higher direct images of `ℓ`-adic towers along smooth proper morphisms give lisse sheaves

Let `K` be a field, `Y` a connected scheme of finite type over `K`, `f : X ⟶ Y` smooth and proper,
`ℓ` a prime invertible in `K`, `Λ = ULift ℤ_ℓ` and `(Gₙ)` an `ℓ`-adic tower of étale sheaves of
`Λ`-modules on `X` whose terms are finite locally constant sheaves of `Λ ⧸ Iₙ`-modules. For every
`j`, the tower `Hₙ = Rʲf_* Gₙ` is killed levelwise by `ℓⁿ`, hence transports to a tower `Mₙ` of
pro-étale `ℤ_ℓ,Y`-modules (`AlgebraicGeometry.ProEtale.comparisonPadicIntModTower`), and
`ℚ̄_ℓ ⊗ lim Mₙ` is lisse
(`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_homology_rightDerivedLowerStar`).

The proof: by `AlgebraicGeometry.Etale.exists_adicTowerStructure_homology_rightDerivedLowerStar`
there is an exact `ℓ`-adic tower `G'` of rank `r`, étale locally `(Λ / ℓᵐ)ʳ`, with a monomorphism
of towers `G' ⟶ (H_{m+c})ₘ` whose cokernels are killed by `ℓ²ᶜ`. The rationalised limit of the
transport of `G'` is lisse
(`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_comparisonPadicIntModTower`),
and rationalised limits are invariant under bounded isogenies and shifts of towers
(`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_comparisonPadicIntModTower_iff`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

/-- The quotient of `ULift ℤ_[p]` by `pⁿ` is additively `ℤ/pⁿ`. -/
noncomputable def ULift.padicIntQuotientSpanPowAddEquiv (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ULift.{v} ℤ_[p] ⧸ Ideal.span {(p : ULift.{v} ℤ_[p]) ^ n} ≃+ ZMod (p ^ n) :=
  ((Ideal.quotientEquiv _ (Ideal.span {(p : ℤ_[p]) ^ n}) ULift.ringEquiv (by
      rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast])).trans
    ((Ideal.quotEquivOfEq (PadicInt.ker_toZModPow n).symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective (PadicInt.toZModPow n))))).toAddEquiv

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} (l : ℕ) [Fact l.Prime]

/-- The shift `n ↦ n + c` of `ℕᵒᵖ`. -/
abbrev natAddOpFunctor (c : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (Monotone.functor (f := fun n : ℕ ↦ n + c) fun _ _ h ↦ Nat.add_le_add_right h c).op

variable {l} in
/-- The morphism of pro-étale towers of `ℤ_ℓ,X`-modules `ν^* G ⟶ (ν^* H_{n+c})ₙ` induced by a
morphism of étale towers `G ⟶ (H_{n+c})ₙ`. -/
noncomputable def comparisonPadicIntModTowerShiftMap
    {G H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0}
    {hH : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (H.obj (op n)) = 0} {c : ℕ}
    (φ : G ⟶ H.towerShift c) :
    comparisonPadicIntModTower X l G hG ⟶
      natAddOpFunctor c ⋙ comparisonPadicIntModTower X l H hH where
  app n := padicIntModHomOfTorsion ((comparisonUpperStarAb Λ X).map (φ.app n))
    (zsmul_id_comparisonUpperStarAb_obj_eq_zero (hH (n.unop + c)))
  naturality _ _ f := Mod.hom_ext _ _ (by
    simp only [Mod.comp_hom']
    exact ((comparisonUpperStarAb Λ X).map_comp _ _).symm.trans
      (((comparisonUpperStarAb Λ X).congr_map (φ.naturality f)).trans
        ((comparisonUpperStarAb Λ X).map_comp _ _)))

variable {l} in
/-- If the components of a morphism of étale towers `φ : G ⟶ (H_{n+c})ₙ` have kernels killed by
`k`, so do those of the induced morphism of pro-étale towers of `ℤ_ℓ,X`-modules. -/
lemma zsmul_kernel_ι_comparisonPadicIntModTowerShiftMap_app_eq_zero
    {G H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0}
    {hH : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (H.obj (op n)) = 0} {c : ℕ}
    (φ : G ⟶ H.towerShift c) {k : ℤ} (h : ∀ n, k • kernel.ι (φ.app n) = 0) (n : ℕᵒᵖ) :
    k • kernel.ι ((comparisonPadicIntModTowerShiftMap (hG := hG) (hH := hH) φ).app n) = 0 :=
  (Mod.forget (padicIntAbSheaf X l)).zsmul_kernel_ι_eq_zero_of_map _
    ((comparisonUpperStarAb Λ X).zsmul_kernel_ι_map_eq_zero _ (h n))

variable {l} in
/-- If the components of a morphism of étale towers `φ : G ⟶ (H_{n+c})ₙ` have cokernels killed
by `k`, so do those of the induced morphism of pro-étale towers of `ℤ_ℓ,X`-modules. -/
lemma zsmul_cokernel_π_comparisonPadicIntModTowerShiftMap_app_eq_zero
    {G H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0}
    {hH : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (H.obj (op n)) = 0} {c : ℕ}
    (φ : G ⟶ H.towerShift c) {k : ℤ} (h : ∀ n, k • cokernel.π (φ.app n) = 0) (n : ℕᵒᵖ) :
    k • cokernel.π ((comparisonPadicIntModTowerShiftMap (hG := hG) (hH := hH) φ).app n) = 0 :=
  (Mod.forget (padicIntAbSheaf X l)).zsmul_cokernel_π_eq_zero_of_map _
    ((comparisonUpperStarAb Λ X).zsmul_cokernel_π_map_eq_zero _ (h n))

/-- **Rationalised limits of transported towers are invariant under shifted bounded isogenies**:
let `φ : G ⟶ (H_{n+c})ₙ` be a morphism of étale towers (with `ℓⁿ Gₙ = 0`, `ℓⁿ Hₙ = 0`) whose
components have kernels killed by `ℓᵃ` and cokernels killed by `ℓᵇ`. Then `ℚ̄_ℓ ⊗ lim ν^* Gₙ` is
lisse if and only if `ℚ̄_ℓ ⊗ lim ν^* Hₙ` is, the limits being taken in `ℤ_ℓ,X`-modules. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_limit_comparisonPadicIntModTower_iff
    {G H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0)
    (hH : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (H.obj (op n)) = 0) {c : ℕ}
    (φ : G ⟶ H.towerShift c) {a b : ℕ} (ha : ∀ n, ((l ^ a : ℕ) : ℤ) • kernel.ι (φ.app n) = 0)
    (hb : ∀ n, ((l ^ b : ℕ) : ℤ) • cokernel.π (φ.app n) = 0) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj
        (limit (comparisonPadicIntModTower X l G hG))) ↔
      IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj
        (limit (comparisonPadicIntModTower X l H hH))) :=
  (isAdicLisseSheaf_adicSheafExtendScalars_limit_iff_of_zsmul_kernel_ι_app_eq_zero l
    (comparisonPadicIntModTowerShiftMap (hG := hG) (hH := hH) φ)
    (natCast_prime_pow_ne_zero l a) (natCast_prime_pow_ne_zero l b)
    (zsmul_kernel_ι_comparisonPadicIntModTowerShiftMap_app_eq_zero φ ha)
    (zsmul_cokernel_π_comparisonPadicIntModTowerShiftMap_app_eq_zero φ hb)).trans
    (isAdicLisseSheaf_adicSheafExtendScalars_limit_shift_iff l c _)

omit [Fact l.Prime] in
/-- The higher direct images `Rʲf_* Gₙ` of an `ℓ`-adic tower are killed by `ℓⁿ`. -/
lemma zsmul_id_homology_rightDerivedLowerStar_eq_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (A : AdicTowerStructure G l)
    (j : ℕ) (n : ℕ) :
    ((l ^ n : ℕ) : ℤ) • 𝟙 ((G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
      R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
        DerivedCategory.homologyFunctor _ j).obj (op n)) = 0 := by
  rw [natCast_zsmul]
  exact Functor.pow_smul_id_eq_zero_of_adicTowerStructure l A _ n

/-- **Higher direct images of `ℓ`-adic towers along smooth proper morphisms give lisse
`ℓ`-adic sheaves.** Let `K` be a field, `Y` a connected scheme of finite type over `K`,
`f : X ⟶ Y` smooth and proper, `ℓ` a prime invertible in `K` and `(Gₙ)` an `ℓ`-adic tower of
étale sheaves of `ULift ℤ_ℓ`-modules on `X`, each `Gₙ` being the restriction of scalars of a
finite locally constant sheaf of `Λ ⧸ Iₙ`-modules. Then for every `j`, transporting the tower
`Rʲf_* Gₙ` to pro-étale `ℤ_ℓ,Y`-modules, `ℚ̄_ℓ ⊗ lim_n ν^* Rʲf_* Gₙ` is lisse. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_limit_homology_rightDerivedLowerStar
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] [ConnectedSpace Y] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])))
    (A : AdicTowerStructure G l) (I : ℕ → Ideal (ULift.{u + 1} ℤ_[l]))
    [∀ n, Finite (ULift.{u + 1} ℤ_[l] ⧸ I n)]
    [∀ n, HasInvertibleExponent (ULift.{u + 1} ℤ_[l] ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l] ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (j : ℕ) :
    IsAdicLisseSheaf ((adicSheafExtendScalars Y l).obj (limit (comparisonPadicIntModTower Y l
      (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        R(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) ⋙
          DerivedCategory.homologyFunctor _ j)
      (zsmul_id_homology_rightDerivedLowerStar_eq_zero l f A j)))) := by
  obtain ⟨c, r, G', A', φ, -, hcok, hmono, hcokφ, -, hcov⟩ :=
    Etale.exists_adicTowerStructure_homology_rightDerivedLowerStar aY f l G A I F eG
      (ULift.natCast_ne_zero_padicInt l) (ULift.not_isUnit_natCast_padicInt l) j
  have hG' := zsmul_id_eq_zero_of_adicTowerStructure Y l A'
  refine (isAdicLisseSheaf_adicSheafExtendScalars_limit_comparisonPadicIntModTower_iff l hG' _ φ
    (a := 0) (b := c + c) (fun n ↦ ?_) (fun n ↦ ?_)).1
    (isAdicLisseSheaf_adicSheafExtendScalars_limit_comparisonPadicIntModTower Y l r G' hG'
      (fun n ↦ ?_) (fun n ↦ ?_))
  · have := hmono n.unop
    rw [kernel.ι_of_mono, smul_zero]
  · rw [natCast_zsmul]
    exact hcokφ n.unop
  · obtain ⟨w, ⟨hc⟩⟩ := hcok n.le_succ
    have e : ((l ^ n : ℕ) : ℤ) • 𝟙 (G'.obj (op (n + 1))) = l ^ n • 𝟙 (G'.obj (op (n + 1))) :=
      natCast_zsmul _ _
    have w' : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫ G'.map (homOfLE n.le_succ).op = 0 := by
      rw [e]
      exact w
    exact ⟨w', ⟨isColimitCokernelCoforkOfEq e.symm w w' hc⟩⟩
  · obtain ⟨𝒰, h𝒰⟩ := hcov n
    exact ⟨𝒰.I₀, 𝒰.X, 𝒰.f, 𝒰.mem₀, fun i ↦ ⟨_,
      ⟨AddEquiv.piCongrRight fun _ ↦ ULift.padicIntQuotientSpanPowAddEquiv l n⟩, h𝒰 i⟩⟩

end AlgebraicGeometry.ProEtale
