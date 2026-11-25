/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.TraceFormula.Specialization.DefectCentreMap
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorTriangulated

/-!

# The exchange squares of the zero-section map

Let `f : X' ⟶ X` be a morphism of `k`-schemes, `Z = V(I) ⊆ X`, `Z' = f⁻¹ Z` and `f_Z : Z' ⟶ Z`
the restriction of `f`. Write `ε_{X,Z}(L) : Le^* Ψ_X(L) ⟶ Ψ_Z(Li^* L)` for the zero-section map
(`ProEtale.CondensedRing.zeroSectionMap`), `f̃ : 𝒟_{Z'} X' ⟶ 𝒟_Z X` and `f̃_Z : Z' × S ⟶ Z × S` for
the morphisms of models induced by `f`, with special fibres `f_s` and `g_s`.

This file proves, for arbitrary coefficients, the commutative squares of the proof of blueprint
`lemma-base-change-cone-x-z`:

* the *pullback square* (`ProEtale.CondensedRing.zeroSectionMap_upperStar_square`): through the
  pullback exchanges `α_{f̃}` and `α_{f̃_Z}`, `Lg_s^* ε_{X,Z}(L)` corresponds to
  `ε_{X',Z'}(Lf^* L)`;
  it is the square law of the pullback exchanges
  (`ProEtale.CondensedRing.NearbyCyclesModel.Hom.pullbackExchange_square`) for
  `f̃ ∘ ẽ' = ẽ ∘ f̃_Z`;
* the *pushforward square* (`ProEtale.CondensedRing.zeroSectionMap_lowerStar_square`): through the
  pushforward exchanges `χ_{f̃}`, `χ_{f̃_Z}` and the base change morphisms of the squares
  `e' ≫ f_s = g_s ≫ e` and `i' ≫ f = f_Z ≫ i`, `ε_{X,Z}(Rf_* L')` corresponds to
  `Rg_{s*} ε_{X',Z'}(L')`; both sides have the same adjoint for `Lg_s^* ⊣ Rg_{s*}`, by the pullback
  square.

It also proves the triangulated step of blueprint `lemma-base-change-cone-x-z`
(`ProEtale.CondensedRing.nonempty_specializationDefect_iso_of_distTriang`): for a distinguished
triangle `A ⟶ B ⟶ D ⟶ A[1]` with `Ψ_Z(Li^* A) = 0` and `ε_{X,Z}(D)` invertible,
`C_{X,Z}(A) ≅ C_{X,Z}(B)`, both being `Le^* Ψ_X(A)[1]`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The commutative squares of the zero sections -/

/-- The square `i' ≫ f = f_Z ≫ i` of the centres. -/
lemma centreι_comp_eq_centreMap_comp :
    (centreι X' (I.comap f.left)).left ≫ f.left = (centreMap f I).left ≫ (centreι X I).left :=
  (congrArg CommaMorphism.left (centreMap_centreι f I)).symm

/-- The square `e' ≫ f_s = g_s ≫ e` of the zero sections of the special fibres. -/
lemma zeroSectionSpecialFibreMap_comp_eq :
    (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left ≫
        (comapSpecialFibreMap f I k').left =
      (centreSpecialFibreMap f I k').left ≫ (zeroSectionSpecialFibreMap X I k').left :=
  (isPullback_zeroSectionSpecialFibreMap f I k').w

/-- **The pullback square of the zero-section maps**: through the pullback exchanges of
`f̃ : 𝒟_{Z'} X' ⟶ 𝒟_Z X` and `f̃_Z : Z' × S ⟶ Z × S`,
`α_{ẽ'}(Lf^* K) ∘ Le'^* α_{f̃}(K) ∘ θ = Ψ_{Z'}(θ) ∘ α_{f̃_Z}(Li^* K) ∘ Lg_s^* ε_{X,Z}(K)`, where the
`θ` are the comparisons of the squares `e' ≫ f_s = g_s ≫ e` and `i' ≫ f = f_Z ≫ i`. -/
lemma zeroSectionMap_upperStar_square
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    (pullbackSquareComparison Λ (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
        CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
          (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
          (zeroSectionSpecialFibreMap X I k').left)).hom.app
        (((deformationModel X I k').nearbyCycles Λ).obj K) ≫
      L(((zeroSectionSpecialFibreMap X' (I.comap f.left) k').left)^*⟦Λ⟧).map
        (((comapDeformationModelHom f I k').pullbackExchange Λ).app K) ≫
      zeroSectionMap X' (I.comap f.left) k' Λ (L((f.left)^*⟦Λ⟧).obj K) =
    L(((centreSpecialFibreMap f I k').left)^*⟦Λ⟧).map (zeroSectionMap X I k' Λ K) ≫
      ((centreDeformationModelHom f I k').pullbackExchange Λ).app
        (L(((centreι X I).left)^*⟦Λ⟧).obj K) ≫
      ((deformationModel (centre X' (I.comap f.left)) ⊥ k').nearbyCycles Λ).map
        ((pullbackSquareComparison Λ (⟨centreι_comp_eq_centreMap_comp f I⟩ :
          CommSq (centreι X' (I.comap f.left)).left (centreMap f I).left f.left
            (centreι X I).left)).hom.app K) :=
  NearbyCyclesModel.Hom.pullbackExchange_square Λ
    (zeroSectionDeformationModelHom X' (I.comap f.left) k') (comapDeformationModelHom f I k')
    (centreDeformationModelHom f I k') (zeroSectionDeformationModelHom X I k')
    (zeroSectionDeformationModelHom_total_comp f I k')
    (zeroSectionDeformationModelHom_generic_comp f I k')
    (centreι_comp_eq_centreMap_comp f I) (zeroSectionSpecialFibreMap_comp_eq f I k') K



/-- The abstract shape of `zeroSectionMap_lowerStar_square`: for adjunctions `f^* ⊣ f_*`,
`f_Z^* ⊣ f_{Z*}`, `f_s^* ⊣ f_{s*}`, `g_s^* ⊣ g_{s*}`, natural transformations `α`, `χ` related by
the counit identities, zero-section maps `ε`, `ε'`, comparisons `θ_i`, `θ_e` satisfying the
pullback square, and base change morphisms `β_i`, `β_e` (the exchanges of `θ_i`, `θ_e`), the
pushforward square commutes. -/
lemma zeroSectionMap_lowerStar_square_aux {DX DX' DZ DZ' SX SX' SZ SZ' : Type*} [Category DX]
    [Category DX'] [Category DZ] [Category DZ'] [Category SX] [Category SX'] [Category SZ]
    [Category SZ'] {fu : DX ⥤ DX'} {fl : DX' ⥤ DX} {fZu : DZ ⥤ DZ'} {fZl : DZ' ⥤ DZ}
    {fsu : SX ⥤ SX'} {fsl : SX' ⥤ SX} {gsu : SZ ⥤ SZ'} {gsl : SZ' ⥤ SZ}
    {iu : DX ⥤ DZ} {iu' : DX' ⥤ DZ'} {eu : SX ⥤ SZ} {eu' : SX' ⥤ SZ'}
    {ΨX : DX ⥤ SX} {ΨX' : DX' ⥤ SX'} {ΨZ : DZ ⥤ SZ} {ΨZ' : DZ' ⥤ SZ'}
    (af : fu ⊣ fl) (afZ : fZu ⊣ fZl) (afs : fsu ⊣ fsl) (ags : gsu ⊣ gsl)
    (αf : ΨX ⋙ fsu ⟶ fu ⋙ ΨX') (χf : fl ⋙ ΨX ⟶ ΨX' ⋙ fsl)
    (αg : ΨZ ⋙ gsu ⟶ fZu ⋙ ΨZ') (χg : fZl ⋙ ΨZ ⟶ ΨZ' ⋙ gsl)
    (ε : ∀ K, eu.obj (ΨX.obj K) ⟶ ΨZ.obj (iu.obj K))
    (ε' : ∀ K, eu'.obj (ΨX'.obj K) ⟶ ΨZ'.obj (iu'.obj K))
    (hε' : ∀ {K L : DX'} (φ : K ⟶ L), eu'.map (ΨX'.map φ) ≫ ε' L = ε' K ≫ ΨZ'.map (iu'.map φ))
    (θe : eu ⋙ gsu ≅ fsu ⋙ eu') (θi : iu ⋙ fZu ≅ fu ⋙ iu')
    (βi : fl ⋙ iu ⟶ iu' ⋙ fZl) (βe : fsl ⋙ eu ⟶ eu' ⋙ gsl)
    (hβi : ∀ K, fZu.map (βi.app K) ≫ afZ.counit.app (iu'.obj K) =
      θi.hom.app (fl.obj K) ≫ iu'.map (af.counit.app K))
    (hβe : ∀ K, gsu.map (βe.app K) ≫ ags.counit.app (eu'.obj K) =
      θe.hom.app (fsl.obj K) ≫ eu'.map (afs.counit.app K))
    (hχf : ∀ E, fsu.map (χf.app E) ≫ afs.counit.app (ΨX'.obj E) =
      αf.app (fl.obj E) ≫ ΨX'.map (af.counit.app E))
    (hχg : ∀ E, gsu.map (χg.app E) ≫ ags.counit.app (ΨZ'.obj E) =
      αg.app (fZl.obj E) ≫ ΨZ'.map (afZ.counit.app E))
    (hsq : ∀ K, θe.hom.app (ΨX.obj K) ≫ eu'.map (αf.app K) ≫ ε' (fu.obj K) =
      gsu.map (ε K) ≫ αg.app (iu.obj K) ≫ ΨZ'.map (θi.hom.app K))
    (L' : DX') :
    ε (fl.obj L') ≫ ΨZ.map (βi.app L') ≫ χg.app (iu'.obj L') =
      eu.map (χf.app L') ≫ βe.app (ΨX'.obj L') ≫ gsl.map (ε' L') := by
  apply (ags.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, hχg,
    Adjunction.counit_naturality]
  have hL := αg.naturality (βi.app L')
  simp only [Functor.comp_map] at hL
  rw [reassoc_of% hL, ← ΨZ'.map_comp, hβi, reassoc_of% (hβe (ΨX'.obj L'))]
  have hθ := θe.hom.naturality (χf.app L')
  simp only [Functor.comp_map] at hθ
  have hε := hε' (af.counit.app L')
  simp only [Functor.id_obj, Functor.comp_obj] at hε
  rw [reassoc_of% hθ, ← eu'.map_comp_assoc, hχf, eu'.map_comp, Category.assoc, hε,
    reassoc_of% (hsq (fl.obj L'))]
  simp only [Functor.map_comp]

/-- **The pushforward square of the zero-section maps**: through the pushforward exchanges `χ` of
`f̃ : 𝒟_{Z'} X' ⟶ 𝒟_Z X` and `f̃_Z : Z' × S ⟶ Z × S` and the base change morphisms `β` of the
squares `i' ≫ f = f_Z ≫ i` and `e' ≫ f_s = g_s ≫ e`,
`χ_{f̃_Z}(Li'^* L') ∘ Ψ_Z(β(L')) ∘ ε_{X,Z}(Rf_* L') = Rg_{s*} ε_{X',Z'}(L') ∘ β(Ψ_{X'} L') ∘
Le^* χ_{f̃}(L')`. Both sides have the same adjoint for `Lg_s^* ⊣ Rg_{s*}`, by the pullback square
`zeroSectionMap_upperStar_square` and the counit identities of the exchanges. -/
lemma zeroSectionMap_lowerStar_square
    (L' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1})
      (condensedRingObj Λ X'.left))) :
    zeroSectionMap X I k' Λ (R((f.left)_*⟦Λ⟧).obj L') ≫
        ((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).map
          ((baseChangeMap Λ (⟨centreι_comp_eq_centreMap_comp f I⟩ :
            CommSq (centreι X' (I.comap f.left)).left (centreMap f I).left f.left
              (centreι X I).left)).app L') ≫
        ((centreDeformationModelHom f I k').pushforwardExchange Λ).app
          (L(((centreι X' (I.comap f.left)).left)^*⟦Λ⟧).obj L') =
      L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
          (((comapDeformationModelHom f I k').pushforwardExchange Λ).app L') ≫
        (baseChangeMap Λ (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
          CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
            (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
            (zeroSectionSpecialFibreMap X I k').left)).app
          (((deformationModel X' (I.comap f.left) k').nearbyCycles Λ).obj L') ≫
        R(((centreSpecialFibreMap f I k').left)_*⟦Λ⟧).map
          (zeroSectionMap X' (I.comap f.left) k' Λ L') :=
  zeroSectionMap_lowerStar_square_aux (derivedUpperStarLowerStarAdjunction Λ f.left)
    (derivedUpperStarLowerStarAdjunction Λ (centreMap f I).left)
    (derivedUpperStarLowerStarAdjunction Λ (comapSpecialFibreMap f I k').left)
    (derivedUpperStarLowerStarAdjunction Λ (centreSpecialFibreMap f I k').left)
    ((comapDeformationModelHom f I k').pullbackExchange Λ)
    ((comapDeformationModelHom f I k').pushforwardExchange Λ)
    ((centreDeformationModelHom f I k').pullbackExchange Λ)
    ((centreDeformationModelHom f I k').pushforwardExchange Λ)
    (zeroSectionMap X I k' Λ) (zeroSectionMap X' (I.comap f.left) k' Λ)
    (zeroSectionMap_naturality X' (I.comap f.left) k' Λ)
    (pullbackSquareComparison Λ (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
      CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
        (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
        (zeroSectionSpecialFibreMap X I k').left))
    (pullbackSquareComparison Λ (⟨centreι_comp_eq_centreMap_comp f I⟩ :
      CommSq (centreι X' (I.comap f.left)).left (centreMap f I).left f.left (centreι X I).left))
    (baseChangeMap Λ (⟨centreι_comp_eq_centreMap_comp f I⟩ :
      CommSq (centreι X' (I.comap f.left)).left (centreMap f I).left f.left (centreι X I).left))
    (baseChangeMap Λ (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
      CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
        (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
        (zeroSectionSpecialFibreMap X I k').left))
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    ((comapDeformationModelHom f I k').map_pushforwardExchange_app_comp_counit_app Λ)
    ((centreDeformationModelHom f I k').map_pushforwardExchange_app_comp_counit_app Λ)
    (zeroSectionMap_upperStar_square f I k' Λ) L'

/-! ### The defect along a distinguished triangle -/

/-- The abstract shape of `nonempty_specializationDefect_iso_of_distTriang`: in a pretriangulated
category, let `ε : TF ⟶ TG` be maps between the terms of distinguished triangles, natural on the
second morphisms, with `TG.obj₁ = 0` and `ε₃` invertible. Then the cones of `ε₁` and `ε₂` are
isomorphic: both are `TF.obj₁[1]`. -/
lemma nonempty_iso_cone_of_distTriang_aux {D : Type*} [Category D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (TF TG : Triangle D) (hF : TF ∈ distTriang D) (hG : TG ∈ distTriang D)
    (hGA : IsZero TG.obj₁) (ε₁ : TF.obj₁ ⟶ TG.obj₁) (ε₂ : TF.obj₂ ⟶ TG.obj₂)
    (ε₃ : TF.obj₃ ⟶ TG.obj₃) [IsIso ε₃] (hnat : TF.mor₂ ≫ ε₃ = ε₂ ≫ TG.mor₂)
    {CA CB : D} (uA : TG.obj₁ ⟶ CA) (vA : CA ⟶ TF.obj₁⟦(1 : ℤ)⟧) (uB : TG.obj₂ ⟶ CB)
    (vB : CB ⟶ TF.obj₂⟦(1 : ℤ)⟧) (hA : Triangle.mk ε₁ uA vA ∈ distTriang D)
    (hB : Triangle.mk ε₂ uB vB ∈ distTriang D) : Nonempty (CA ≅ CB) := by
  obtain ⟨φ₁, -, -⟩ := exists_iso_of_arrow_iso _ _ hA (contractible_distinguished₂ TF.obj₁)
    (Arrow.isoMk (Iso.refl _) (hGA.iso (isZero_zero _)) ((isZero_zero _).eq_of_tgt _ _))
  have : IsIso TG.mor₂ := (Triangle.isZero₁_iff_isIso₂ _ hG).1 hGA
  obtain ⟨φ₂, -, -⟩ := exists_iso_of_arrow_iso _ _ hB (rot_of_distTriang _ hF)
    (Arrow.isoMk (Iso.refl _) (asIso TG.mor₂ ≪≫ (asIso ε₃).symm) (by
      simp [← reassoc_of% hnat]))
  exact ⟨Triangle.π₃.mapIso φ₁ ≪≫ (Triangle.π₃.mapIso φ₂).symm⟩

/-- Cones of morphisms identified through a square of composites of isomorphisms are isomorphic:
the transport of `Pretriangulated.exists_iso_of_arrow_iso` used for the exchanges of the defect. -/
lemma nonempty_iso_obj₃_of_comp_aux {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T₁ T₂ : Triangle D) (h₁ : T₁ ∈ distTriang D) (h₂ : T₂ ∈ distTriang D) {P R : D}
    (a : T₁.obj₁ ⟶ P) (b : P ⟶ T₂.obj₁) (c : T₁.obj₂ ⟶ R) (d : R ⟶ T₂.obj₂) [IsIso a] [IsIso b]
    [IsIso c] [IsIso d] (w : a ≫ b ≫ T₂.mor₁ = T₁.mor₁ ≫ c ≫ d) :
    Nonempty (T₁.obj₃ ≅ T₂.obj₃) := by
  obtain ⟨φ, -, -⟩ := exists_iso_of_arrow_iso _ _ h₁ h₂
    (Arrow.isoMk (asIso (a ≫ b)) (asIso (c ≫ d)) (by simpa using w))
  exact ⟨Triangle.π₃.mapIso φ⟩

/-- **The defect along a triangle whose first term is killed by `Ψ_Z Li^*`** (the triangulated step
of blueprint `lemma-base-change-cone-x-z`): for a distinguished triangle `A ⟶ B ⟶ D ⟶ A[1]`
with `Ψ_Z(Li^* A) = 0` and `ε_{X,Z}(D)` invertible, `C_{X,Z}(A) ≅ C_{X,Z}(B)`. Indeed both are
`Le^* Ψ_X(A)[1]`: the first since `ε_{X,Z}(A)` has target zero, the second since `ε_{X,Z}(B)` is
`Le^* Ψ_X(B ⟶ D)` up to the isomorphisms `Ψ_Z Li^*(B) ≅ Ψ_Z Li^*(D)` and `ε_{X,Z}(D)`. -/
theorem nonempty_specializationDefect_iso_of_distTriang
    {T : Triangle (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))} (hT : T ∈ distTriang _)
    (h₁ : IsZero (((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).obj
      (L(((centreι X I).left)^*⟦Λ⟧).obj T.obj₁)))
    (h₃ : IsIso (zeroSectionMap X I k' Λ T.obj₃)) :
    Nonempty (specializationDefect X I k' Λ T.obj₁ ≅ specializationDefect X I k' Λ T.obj₂) := by
  have hF := ((deformationModel X I k').nearbyCycles Λ ⋙
    L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧)).map_distinguished T hT
  have hG := (L(((centreι X I).left)^*⟦Λ⟧) ⋙
    (deformationModel (centre X I) ⊥ k').nearbyCycles Λ).map_distinguished T hT
  obtain ⟨g₁, k₁, hT₁⟩ := exists_distTriang_specializationDefect X I k' Λ T.obj₁
  obtain ⟨g₂, k₂, hT₂⟩ := exists_distTriang_specializationDefect X I k' Λ T.obj₂
  exact nonempty_iso_cone_of_distTriang_aux _ _ hF hG h₁ (zeroSectionMap X I k' Λ T.obj₁)
    (zeroSectionMap X I k' Λ T.obj₂) (zeroSectionMap X I k' Λ T.obj₃)
    (zeroSectionMap_naturality X I k' Λ T.mor₂) g₁ k₁ g₂ k₂ hT₁ hT₂

/-! ### The exchanges of the defect -/

-- The defeq checks of `Functor.mapTriangle` on the derived categories exceed the default limit.
/-- **Smooth exchange for the defect, given the smooth exchanges of nearby cycles**: if the
pullback exchanges of `f̃ : 𝒟_{Z'} X' ⟶ 𝒟_Z X` at `L` and of `f̃_Z : Z' × S ⟶ Z × S` at `Li^* L` are
invertible, then `C_{X',Z'}(Lf^* L) ≅ Lg_s^* C_{X,Z}(L)`: these exchanges carry
`Lg_s^* ε_{X,Z}(L)` to `ε_{X',Z'}(Lf^* L)` (`zeroSectionMap_upperStar_square`). -/
theorem nonempty_specializationDefect_upperStar_iso_of_isIso
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hf : IsIso (((comapDeformationModelHom f I k').pullbackExchange Λ).app L))
    (hg : IsIso (((centreDeformationModelHom f I k').pullbackExchange Λ).app
      (L(((centreι X I).left)^*⟦Λ⟧).obj L))) :
    Nonempty (specializationDefect X' (I.comap f.left) k' Λ (L((f.left)^*⟦Λ⟧).obj L) ≅
      L(((centreSpecialFibreMap f I k').left)^*⟦Λ⟧).obj (specializationDefect X I k' Λ L)) := by
  have hw := zeroSectionMap_upperStar_square f I k' Λ L
  obtain ⟨g, h, hT⟩ := exists_distTriang_specializationDefect X I k' Λ L
  have hT₂ := (L(((centreSpecialFibreMap f I k').left)^*⟦Λ⟧)).map_distinguished _ hT
  have hT' := (exists_distTriang_specializationDefect X' (I.comap f.left) k' Λ
    (L((f.left)^*⟦Λ⟧).obj L)).choose_spec.choose_spec
  exact (nonempty_iso_obj₃_of_comp_aux _ _ hT₂ hT' _ _ _ _ hw).map Iso.symm

/-- **Proper exchange for the defect, given the proper exchanges**: if the pushforward exchanges
of `f̃` at `L'` and of `f̃_Z` at `Li'^* L'` and the base change morphisms of the squares
`i' ≫ f = f_Z ≫ i` at `L'` and `e' ≫ f_s = g_s ≫ e` at `Ψ_{X'}(L')` are invertible, then
`C_{X,Z}(Rf_* L') ≅ Rg_{s*} C_{X',Z'}(L')`: these maps carry `ε_{X,Z}(Rf_* L')` to
`Rg_{s*} ε_{X',Z'}(L')` (`zeroSectionMap_lowerStar_square`). -/
theorem nonempty_specializationDefect_lowerStar_iso_of_isIso
    (L' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1})
      (condensedRingObj Λ X'.left)))
    (h₁ : IsIso (((comapDeformationModelHom f I k').pushforwardExchange Λ).app L'))
    (h₂ : IsIso (((centreDeformationModelHom f I k').pushforwardExchange Λ).app
      (L(((centreι X' (I.comap f.left)).left)^*⟦Λ⟧).obj L')))
    (h₃ : IsIso ((baseChangeMap Λ (⟨centreι_comp_eq_centreMap_comp f I⟩ :
      CommSq (centreι X' (I.comap f.left)).left (centreMap f I).left f.left
        (centreι X I).left)).app L'))
    (h₄ : IsIso ((baseChangeMap Λ (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
      CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
        (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
        (zeroSectionSpecialFibreMap X I k').left)).app
      (((deformationModel X' (I.comap f.left) k').nearbyCycles Λ).obj L'))) :
    Nonempty (specializationDefect X I k' Λ (R((f.left)_*⟦Λ⟧).obj L') ≅
      R(((centreSpecialFibreMap f I k').left)_*⟦Λ⟧).obj
        (specializationDefect X' (I.comap f.left) k' Λ L')) := by
  obtain ⟨g, h, hT⟩ := exists_distTriang_specializationDefect X I k' Λ (R((f.left)_*⟦Λ⟧).obj L')
  obtain ⟨g', h', hT'⟩ := exists_distTriang_specializationDefect X' (I.comap f.left) k' Λ L'
  exact nonempty_iso_obj₃_of_comp_aux _ _ hT
    ((R(((centreSpecialFibreMap f I k').left)_*⟦Λ⟧)).map_distinguished _ hT') _ _ _ _
    (zeroSectionMap_lowerStar_square f I k' Λ L').symm


omit [Algebra k k'] in
/-- **The defect of the zero ideal vanishes** (blueprint `lemma-base-change-cone-x-z`, first
assertion): for `J = ⊥`, the zero section `Y × S ⟶ 𝒟_⊥ Y` is an isomorphism of models, so the
zero-section map is invertible and `C_{Y,Y} = 0`. -/
theorem isZero_specializationDefect_of_eq_bot [Algebra k k'] (Y : Over (Spec (.of k)))
    (J : Y.left.IdealSheafData) (hJ : J = ⊥)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))) :
    IsZero (specializationDefect Y J k' Λ L) := by
  subst hJ
  rw [isZero_specializationDefect_iff]
  have := (zeroSectionDeformationModelHom Y ⊥ k').isIso_pullbackExchange_of_isIso Λ
  exact NatIso.isIso_app_of_isIso _ L

end AlgebraicGeometry.ProEtale.CondensedRing
