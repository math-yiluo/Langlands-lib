/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleOfTorsion
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.Abelian.AdicTowerStructure
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-!
# From étale towers of `ℓ`-torsion sheaves to pro-étale towers of `ℤ_ℓ,X`-modules

Let `X` be a scheme, `ℓ` a prime and `Λ` a commutative ring. The functor
`AlgebraicGeometry.ProEtale.comparisonUpperStarAb` sends an étale sheaf of `Λ`-modules `G` to the
abelian sheaf underlying `ν^* G` on `X_proét`. It is exact (it preserves finite limits and all
colimits). When `G` is killed by `ℓⁿ`, so is its image, which is then a `ℤ_ℓ,X`-module
(`AlgebraicGeometry.ProEtale.padicIntModOfTorsion`). Consequently:

* a tower `(Gₙ)` of étale sheaves of `Λ`-modules with `ℓⁿ Gₙ = 0` gives a tower of
  `ℤ_ℓ,X`-modules (`AlgebraicGeometry.ProEtale.comparisonPadicIntModTower`) whose underlying
  tower of abelian sheaves is `ν^* Gₙ`;
* if the transitions of `(Gₙ)` are cokernels of `ℓⁿ`, so are those of the pro-étale tower
  (`AlgebraicGeometry.ProEtale.exists_isColimit_comparisonPadicIntModTower`);
* a morphism of towers whose components have kernels (resp. cokernels) killed by an integer `a`
  gives a morphism of towers of `ℤ_ℓ,X`-modules with the same property
  (`AlgebraicGeometry.ProEtale.zsmul_kernel_ι_comparisonPadicIntModTowerMap_app_eq_zero`,
  `AlgebraicGeometry.ProEtale.zsmul_cokernel_π_comparisonPadicIntModTowerMap_app_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {X Y : C} (f : X ⟶ Y) {k : ℤ}

/-- An additive functor preserving the kernel of `f` sends a kernel killed by `k` to a kernel
killed by `k`. -/
lemma zsmul_kernel_ι_map_eq_zero [HasKernel f] [HasKernel (F.map f)]
    [PreservesLimit (parallelPair f 0) F] (h : k • kernel.ι f = 0) :
    k • kernel.ι (F.map f) = 0 := by
  rw [← PreservesKernel.iso_inv_ι, ← Preadditive.comp_zsmul, ← F.map_zsmul, h, F.map_zero,
    comp_zero]

/-- A faithful additive functor preserving the kernel of `f` reflects the property that the
kernel is killed by `k`. -/
lemma zsmul_kernel_ι_eq_zero_of_map [F.Faithful] [HasKernel f] [HasKernel (F.map f)]
    [PreservesLimit (parallelPair f 0) F] (h : k • kernel.ι (F.map f) = 0) :
    k • kernel.ι f = 0 :=
  F.map_injective (by
    rw [F.map_zsmul, F.map_zero, ← kernelComparison_comp_ι, ← Preadditive.comp_zsmul, h,
      comp_zero])

/-- An additive functor preserving the cokernel of `f` sends a cokernel killed by `k` to a
cokernel killed by `k`. -/
lemma zsmul_cokernel_π_map_eq_zero [HasCokernel f] [HasCokernel (F.map f)]
    [PreservesColimit (parallelPair f 0) F] (h : k • cokernel.π f = 0) :
    k • cokernel.π (F.map f) = 0 := by
  rw [← PreservesCokernel.π_iso_hom, ← Preadditive.zsmul_comp, ← F.map_zsmul, h, F.map_zero,
    zero_comp]

/-- A faithful additive functor preserving the cokernel of `f` reflects the property that the
cokernel is killed by `k`. -/
lemma zsmul_cokernel_π_eq_zero_of_map [F.Faithful] [HasCokernel f] [HasCokernel (F.map f)]
    [PreservesColimit (parallelPair f 0) F] (h : k • cokernel.π (F.map f) = 0) :
    k • cokernel.π f = 0 :=
  F.map_injective (by
    rw [F.map_zsmul, F.map_zero, ← π_comp_cokernelComparison, ← Preadditive.zsmul_comp, h,
      zero_comp])

end CategoryTheory.Functor

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C]

/-- Being a cokernel cofork only depends on the morphism up to equality. -/
noncomputable def isColimitCokernelCoforkOfEq {X Y Z : C} {f f' : X ⟶ Y} (hf : f = f')
    {π : Y ⟶ Z} (w : f ≫ π = 0) (w' : f' ≫ π = 0)
    (h : IsColimit (CokernelCofork.ofπ π w)) : IsColimit (CokernelCofork.ofπ π w') := by
  subst hf
  exact h

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory Abelian.hasFiniteBiproducts

variable {Λ : Type (u + 1)} [CommRing Λ] (X : Scheme.{u})

/-- The forgetful functor from `Λ`-modules to abelian groups is a left adjoint: it is the
restriction of scalars along `ℤ → Λ` followed by the identification of `ℤ`-modules with abelian
groups. -/
instance isLeftAdjoint_forget₂_moduleCat :
    (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).IsLeftAdjoint := by
  have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  exact inferInstanceAs (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1}).IsLeftAdjoint

/-- The underlying abelian sheaf functor on pro-étale sheaves of `Λ`-modules preserves colimits:
it is the sheafified postcomposition with the forgetful functor, a left adjoint. -/
instance preservesColimits_sheafCompose_forget₂ :
    PreservesColimitsOfSize.{u + 1, u + 1} (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})) := by
  let adj := Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})
  have : PreservesLimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).rightAdjoint :=
    adj.rightAdjoint_preservesLimits
  have : (ProEt.topology X).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).rightAdjoint :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction (ProEt.topology X) adj).isLeftAdjoint
  exact preservesColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

/-- The underlying abelian sheaf functor on pro-étale sheaves of `Λ`-modules preserves finite
limits, limits of sheaves being computed on sections. -/
instance preservesFiniteLimits_sheafCompose_forget₂ :
    PreservesFiniteLimits (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})) := by
  have : PreservesFiniteLimits (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

variable (Λ) in
/-- The comparison `ν^*` from étale sheaves of `Λ`-modules to pro-étale abelian sheaves: the
abelian sheaf underlying `ν^* G`. -/
noncomputable def comparisonUpperStarAb :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  ν^*(X)[ModuleCat.{u + 1} Λ] ⋙
    sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})

/-- `ProEtale.comparisonUpperStarAb` is additive. -/
instance : (comparisonUpperStarAb Λ X).Additive :=
  inferInstanceAs (ν^*(X)[ModuleCat.{u + 1} Λ] ⋙
    sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).Additive

/-- `ProEtale.comparisonUpperStarAb` preserves colimits, being a composite of left adjoints. -/
instance : PreservesColimitsOfSize.{u + 1, u + 1} (comparisonUpperStarAb Λ X) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} ν^*(X)[ModuleCat.{u + 1} Λ] :=
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).leftAdjoint_preservesColimits
  exact inferInstanceAs (PreservesColimitsOfSize (ν^*(X)[ModuleCat.{u + 1} Λ] ⋙
    sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})))

/-- `ProEtale.comparisonUpperStarAb` is left exact. -/
instance : PreservesFiniteLimits (comparisonUpperStarAb Λ X) :=
  inferInstanceAs (PreservesFiniteLimits (ν^*(X)[ModuleCat.{u + 1} Λ] ⋙
    sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})))

variable {X} in
/-- `ν^*` preserves the property of being killed by an integer `k`. -/
lemma zsmul_id_comparisonUpperStarAb_obj_eq_zero
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {k : ℤ} (hG : k • 𝟙 G = 0) :
    k • 𝟙 ((comparisonUpperStarAb Λ X).obj G) = 0 := by
  rw [← (comparisonUpperStarAb Λ X).map_id, ← Functor.map_zsmul, hG, Functor.map_zero]

variable (l : ℕ) [Fact l.Prime]

/-- **The pro-étale `ℤ_ℓ,X`-module of an étale sheaf killed by `ℓⁿ`**: the abelian sheaf
underlying `ν^* G`, with its `ℤ_ℓ,X`-module structure `ProEtale.padicIntModOfTorsion`. -/
noncomputable def comparisonPadicIntMod (n : ℕ)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hG : ((l ^ n : ℕ) : ℤ) • 𝟙 G = 0) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l) :=
  padicIntModOfTorsion X l n ((comparisonUpperStarAb Λ X).obj G)
    (zsmul_id_comparisonUpperStarAb_obj_eq_zero hG)

/-- **The pro-étale tower of `ℤ_ℓ,X`-modules of an étale tower** `(Gₙ)` of sheaves of
`Λ`-modules with `ℓⁿ Gₙ = 0`: the tower `ν^* Gₙ`, with the `ℤ_ℓ,X`-module structures of
`ProEtale.padicIntModOfTorsion`. -/
noncomputable def comparisonPadicIntModTower
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0) :
    ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l) :=
  padicIntModTowerOfTorsion X l (G ⋙ comparisonUpperStarAb Λ X)
    fun n ↦ zsmul_id_comparisonUpperStarAb_obj_eq_zero (hG n)

/-- The underlying tower of abelian sheaves of `ProEtale.comparisonPadicIntModTower G hG` is
`ν^* Gₙ`. -/
lemma comparisonPadicIntModTower_comp_forget
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0) :
    comparisonPadicIntModTower X l G hG ⋙ Mod.forget _ = G ⋙ comparisonUpperStarAb Λ X :=
  rfl

omit [Fact l.Prime] in
/-- The towers of an `ℓ`-adic tower structure are killed levelwise: `ℓⁿ Gₙ = 0`. -/
lemma zsmul_id_eq_zero_of_adicTowerStructure
    {G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (A : AdicTowerStructure G l)
    (n : ℕ) : ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0 := by
  rw [natCast_zsmul]
  exact A.pow_smul_id_eq_zero n

/-- **Transitions which are cokernels of `ℓⁿ` are preserved**: if the transitions
`Gₙ₊₁ ⟶ Gₙ` of the étale tower are cokernels of `ℓⁿ`, so are those of the pro-étale tower of
`ℤ_ℓ,X`-modules, `ν^*` being additive and preserving cokernels. This is the hypothesis `hG` of
`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit`. -/
theorem exists_isColimit_comparisonPadicIntModTower
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0)
    (hcok : ∀ n : ℕ, ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫ G.map (homOfLE n.le_succ).op = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w))) (n : ℕ) :
    ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
        (comparisonPadicIntModTower X l G hG ⋙ Mod.forget _).map (homOfLE n.le_succ).op = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)) := by
  obtain ⟨w, ⟨hc⟩⟩ := hcok n
  have e : (comparisonUpperStarAb Λ X).map (((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op (n + 1)))) =
      ((l ^ n : ℕ) : ℤ) • 𝟙 _ := by
    rw [Functor.map_zsmul, CategoryTheory.Functor.map_id]
  have w' : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
      (comparisonUpperStarAb Λ X).map (G.map (homOfLE n.le_succ).op) = 0 := by
    rw [← e, ← Functor.map_comp, w, Functor.map_zero]
  exact ⟨w', ⟨isColimitCokernelCoforkOfEq e
    (by rw [← Functor.map_comp, w, Functor.map_zero]) w'
    (CokernelCofork.mapIsColimit _ hc (comparisonUpperStarAb Λ X))⟩⟩

variable {X l} in
/-- The morphism of pro-étale towers of `ℤ_ℓ,X`-modules induced by a morphism of étale towers. -/
noncomputable def comparisonPadicIntModTowerMap
    {G H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0}
    {hH : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (H.obj (op n)) = 0} (φ : G ⟶ H) :
    comparisonPadicIntModTower X l G hG ⟶ comparisonPadicIntModTower X l H hH where
  app n := padicIntModHomOfTorsion ((comparisonUpperStarAb Λ X).map (φ.app n))
    (zsmul_id_comparisonUpperStarAb_obj_eq_zero (hH n.unop))
  naturality _ _ f := Mod.hom_ext _ _ (by
    simp only [Mod.comp_hom']
    exact ((comparisonUpperStarAb Λ X).map_comp _ _).symm.trans
      (((comparisonUpperStarAb Λ X).congr_map (φ.naturality f)).trans
        ((comparisonUpperStarAb Λ X).map_comp _ _)))

variable {X l} in
/-- The components of `ProEtale.comparisonPadicIntModTowerMap φ` are `ν^*` of those of `φ`. -/
lemma comparisonPadicIntModTowerMap_app_hom
    {G H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0}
    {hH : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (H.obj (op n)) = 0} (φ : G ⟶ H) (n : ℕᵒᵖ) :
    ((comparisonPadicIntModTowerMap (hG := hG) (hH := hH) φ).app n).hom =
      (comparisonUpperStarAb Λ X).map (φ.app n) :=
  rfl

variable {X l} in
/-- **Kernels killed by `k` are preserved**: if the components of a morphism of étale towers
have kernels killed by `k`, so do the components of the induced morphism of pro-étale towers of
`ℤ_ℓ,X`-modules. -/
theorem zsmul_kernel_ι_comparisonPadicIntModTowerMap_app_eq_zero
    {G H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0}
    {hH : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (H.obj (op n)) = 0} (φ : G ⟶ H) {k : ℤ}
    (h : ∀ n, k • kernel.ι (φ.app n) = 0) (n : ℕᵒᵖ) :
    k • kernel.ι ((comparisonPadicIntModTowerMap (hG := hG) (hH := hH) φ).app n) = 0 :=
  (Mod.forget (padicIntAbSheaf X l)).zsmul_kernel_ι_eq_zero_of_map _
    ((comparisonUpperStarAb Λ X).zsmul_kernel_ι_map_eq_zero _ (h n))

variable {X l} in
/-- **Cokernels killed by `k` are preserved**: if the components of a morphism of étale towers
have cokernels killed by `k`, so do the components of the induced morphism of pro-étale towers
of `ℤ_ℓ,X`-modules. -/
theorem zsmul_cokernel_π_comparisonPadicIntModTowerMap_app_eq_zero
    {G H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0}
    {hH : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (H.obj (op n)) = 0} (φ : G ⟶ H) {k : ℤ}
    (h : ∀ n, k • cokernel.π (φ.app n) = 0) (n : ℕᵒᵖ) :
    k • cokernel.π ((comparisonPadicIntModTowerMap (hG := hG) (hH := hH) φ).app n) = 0 :=
  (Mod.forget (padicIntAbSheaf X l)).zsmul_cokernel_π_eq_zero_of_map _
    ((comparisonUpperStarAb Λ X).zsmul_cokernel_π_map_eq_zero _ (h n))

end AlgebraicGeometry.ProEtale
