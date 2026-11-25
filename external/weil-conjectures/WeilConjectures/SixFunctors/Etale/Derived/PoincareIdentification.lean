/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalVerdierDuality
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift

/-!
# The adjoint of the Poincaré pairing is global Verdier duality

Let `a : X ⟶ Y` admit a compactification and satisfy the projection formula, and let
`γ : T[2d] ≅ Ra^! Λ_Y` be a purity isomorphism (for an orientation, `T = Λ_X(d)`). This file
identifies the tensor–internal-hom adjoint of the derived Poincaré pairing

`β_K^♯ : (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨`

(over `Y = Spec k`: `RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨`) with the composite of the purity
identification `K^∨ ⊗ᴸ T[2d] ⟶ RHom(K, ω_X) = 𝔻_X K` and the inverse of the global
Verdier-duality isomorphism `(Ra_! K)^∨ ≅ Ra_* 𝔻_X K`. This is blueprint
`theorem-poincare-duality--7`. As in
`WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing`, `Ra^!` enters only through the
adjunction `Ra_! ⊣ Ra^!`, and the statements are made for an arbitrary right adjoint of `Ra_!`.

## Main definitions

- `AlgebraicGeometry.Etale.exchangePairing`: the pairing
  `Ra_! M ⊗ᴸ Ra_* RHom(M, Ra^! N) ⟶ N` (cup product, evaluation, counit of `Ra_! ⊣ Ra^!`),
  whose adjoint is the tensor–Hom exchange.
- `AlgebraicGeometry.Etale.projectionMapObjObj`: the components of the projection map, with
  source and target written through `Ra_!`, `-⊗ᴸ-` and `La^*`.
- `AlgebraicGeometry.Etale.purityVerdierDualMap`: the purity identification
  `(K^∨ ⊗ᴸ T)[2d] ⟶ 𝔻_X K` attached to `γ`.

## Main statements

- `AlgebraicGeometry.Etale.uncurry_derivedHomLowerShriekIsoOfAdjunction_hom_app_app`:
  the tensor–Hom exchange is the adjoint of `AlgebraicGeometry.Etale.exchangePairing`.
- `AlgebraicGeometry.Etale.isIso_purityVerdierDualMap`: the purity identification is an
  isomorphism for perfect `K`.
- `AlgebraicGeometry.Etale.curry_poincarePairing_eq` (`theorem-poincare-duality--7`):
  `β_K^♯` is the purity identification followed by the inverse of global Verdier duality.
- `AlgebraicGeometry.Etale.inv_curry_poincarePairing_eq`
  (`theorem-poincare-duality--7`): the inverse of `β_K^♯` is global Verdier duality
  followed by the inverse of the purity identification.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

section CupProduct
/-- The projection map `Ra_! K ⊗ᴸ - ⟶ Ra_!(K ⊗ᴸ La^* -)` (`AlgebraicGeometry.Etale.projectionMap`)
at `K`, as a natural transformation with target written as a composite of functors. -/
noncomputable def projectionMapComp (K : 𝐃(X, A)) :
    (derivedTensor A Y).obj ((R(a)_![A]).obj K) ⟶
      L((a)^*[A]) ⋙ (derivedTensor A X).obj K ⋙ R(a)_![A] :=
  (projectionMap A a).app K

instance (K : 𝐃(X, A)) : NatTrans.CommShift (projectionMapComp A a K) ℤ :=
  commShift_projectionMap_app A (f := a) K

/-- The component `Ra_! K ⊗ᴸ M ⟶ Ra_!(K ⊗ᴸ La^* M)` of the projection map
(`AlgebraicGeometry.Etale.projectionMap`). -/
noncomputable def projectionMapObjObj (K : 𝐃(X, A)) (M : 𝐃(Y, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj M ⟶
      (R(a)_![A]).obj (((derivedTensor A X).obj K).obj ((L((a)^*[A])).obj M)) :=
  (projectionMapComp A a K).app M

omit [HasSmallSiteSheafify A] in
@[reassoc]
lemma projectionMapApp_naturality (K : 𝐃(X, A)) {M M' : 𝐃(Y, A)} (g : M ⟶ M') :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map g ≫ projectionMapObjObj A a K M' =
      projectionMapObjObj A a K M ≫
        (R(a)_![A]).map (((derivedTensor A X).obj K).map ((L((a)^*[A])).map g)) :=
  (projectionMapComp A a K).naturality g

omit [HasSmallSiteSheafify A] in
@[reassoc]
lemma projectionMapApp_shift (K : 𝐃(X, A)) (M : 𝐃(Y, A)) (n : ℤ) :
    (((derivedTensor A Y).obj ((R(a)_![A]).obj K)).commShiftIso n).hom.app M ≫
        (projectionMapObjObj A a K M)⟦n⟧' =
      projectionMapObjObj A a K (M⟦n⟧) ≫
        (R(a)_![A]).map (((derivedTensor A X).obj K).map
          (((L((a)^*[A])).commShiftIso n).hom.app M)) ≫
        (R(a)_![A]).map ((((derivedTensor A X).obj K).commShiftIso n).hom.app
          ((L((a)^*[A])).obj M)) ≫
        ((R(a)_![A]).commShiftIso n).hom.app _ := by
  have h := NatTrans.shift_app_comm (projectionMapComp A a K) n M
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Functor.comp_map] at h
  exact h

omit [HasSmallSiteSheafify A] in
@[reassoc]
lemma projectionMapApp_naturality_commShiftIso_inv (K L : 𝐃(X, A)) (n : ℤ) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map
        (((R((a)_*[A])).commShiftIso n).inv.app L) ≫
      projectionMapObjObj A a K ((R((a)_*[A])).obj (L⟦n⟧)) =
    projectionMapObjObj A a K (((R((a)_*[A])).obj L)⟦n⟧) ≫
      (R(a)_![A]).map (((derivedTensor A X).obj K).map ((L((a)^*[A])).map
        (((R((a)_*[A])).commShiftIso n).inv.app L))) :=
  projectionMapApp_naturality A a K _

omit [HasSmallSiteSheafify A] in
lemma mixedSupportCupProduct_eq_projectionMapApp (K L : 𝐃(X, A)) :
    mixedSupportCupProduct A a K L =
      projectionMapObjObj A a K ((R((a)_*[A])).obj L) ≫
        (R(a)_![A]).map (((derivedTensor A X).obj K).map
          ((derivedUpperStarLowerStarAdjunction A a).counit.app L)) := by
  rw [mixedSupportCupProduct_eq]
  rfl

omit [HasSmallSiteSheafify A] in
@[reassoc]
lemma commShiftIso_hom_app_comp_mixedSupportCupProduct_shift (K L : 𝐃(X, A)) (n : ℤ) :
    (((derivedTensor A Y).obj ((R(a)_![A]).obj K)).commShiftIso n).hom.app _ ≫
        (mixedSupportCupProduct A a K L)⟦n⟧' ≫ ((R(a)_![A]).commShiftIso n).inv.app _ =
      ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map
          (((R((a)_*[A])).commShiftIso n).inv.app L) ≫
        mixedSupportCupProduct A a K (L⟦n⟧) ≫
          (R(a)_![A]).map ((((derivedTensor A X).obj K).commShiftIso n).hom.app L) := by
  rw [mixedSupportCupProduct_eq_projectionMapApp, mixedSupportCupProduct_eq_projectionMapApp]
  simp only [Category.assoc]
  rw [projectionMapApp_naturality_commShiftIso_inv_assoc, Functor.map_comp, Category.assoc,
    projectionMapApp_shift_assoc]
  congr 1
  rw [← Functor.commShiftIso_hom_naturality_assoc]
  simp only [Functor.id_obj, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  simp only [← Functor.map_comp]
  congr 1
  rw [← Functor.commShiftIso_hom_naturality, Adjunction.shift_counit_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end CupProduct

section Exchange

variable {G : 𝐃(Y, A) ⥤ 𝐃(X, A)} (adj : R(a)_![A] ⊣ G)

/-- The pairing of the tensor–Hom exchange, for a right adjoint `G` of `Ra_!` (for finite
coefficients, `G = Ra^!`),

`Ra_! M ⊗ᴸ Ra_* RHom(M, G N) ⟶ N`:

the mixed-support cup product, `Ra_!` of the evaluation `M ⊗ᴸ RHom(M, G N) ⟶ G N`, and
the counit of `Ra_! ⊣ G`. Its tensor–internal-hom adjoint is the tensor–Hom exchange
(`AlgebraicGeometry.Etale.uncurry_derivedHomLowerShriekIsoOfAdjunction_hom_app_app`). -/
noncomputable def exchangePairing (M : 𝐃(X, A)) (N : 𝐃(Y, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj M)).obj
        ((R((a)_*[A])).obj ((RHom(X)[A].obj (op M)).obj (G.obj N))) ⟶ N :=
  mixedSupportCupProduct A a M _ ≫
    (R(a)_![A]).map ((derivedTensorHomAdjunction A M).counit.app _) ≫
      adj.counit.app N

omit [HasSmallSiteSheafify A] in
/-- The tensor–Hom exchange `Ra_* RHom(M, G N) ⟶ RHom(Ra_! M, N)`
(`AlgebraicGeometry.Etale.derivedHomLowerShriekIsoOfAdjunction`) is the tensor–internal-hom
adjoint of the pairing `AlgebraicGeometry.Etale.exchangePairing`. -/
theorem uncurry_derivedHomLowerShriekIsoOfAdjunction_hom_app_app [IsIso (projectionMap A a)]
    (M : 𝐃(X, A)) (N : 𝐃(Y, A)) :
    MonoidalClosed.uncurry
        (((derivedHomLowerShriekIsoOfAdjunction A a adj).app (op M)).hom.app N) =
      exchangePairing A a adj M N := by
  obtain ⟨e, he, hPF⟩ : ∃ e, derivedHomLowerShriekIsoOfAdjunction A a adj =
      ((derivedTensorHomAdjunction₂ A X).comp (derivedUpperStarLowerStarAdjunction A a)
        adj).conjugateIso
        ((derivedTensorHomAdjunction₂ A Y).precomp R(a)_![A]) e ∧
      ∀ M' L', (e.hom.app M').app L' = projectionMapObjObj A a M' L' :=
    ⟨_, rfl, fun _ _ ↦ rfl⟩
  rw [he]
  refine (MonoidalClosed.uncurry_eq _).trans
    ((ParametrizedAdjunction.map_conjugateIso_app_hom_app_comp_counit _ _ e (op M) N).trans ?_)
  rw [hPF, exchangePairing, mixedSupportCupProduct_eq_projectionMapApp]
  simp only [ParametrizedAdjunction.comp_adj, Adjunction.comp_counit_app, Category.assoc]
  rfl

end Exchange

section Purity

variable {A} {d : ℕ} {T : 𝐃(X, A)} {G : 𝐃(Y, A) ⥤ 𝐃(X, A)}

/-- The purity identification `(K^∨ ⊗ᴸ T)[2d] ⟶ RHom(K, G Λ_Y)` of an isomorphism
`γ : T[2d] ≅ G Λ_Y`, for a right adjoint `G` of `Ra_!` (for finite coefficients, `G = Ra^!`,
`G Λ_Y = ω_X` and the target is `𝔻_X K`): the tensor–internal-hom adjoint of
```
K ⊗ᴸ (K^∨ ⊗ᴸ T)[2d] ≅ (K ⊗ᴸ (K^∨ ⊗ᴸ T))[2d] --(twisted evaluation)[2d]--> T[2d] --γ--> G Λ_Y.
```
For `T = Λ_X(d)` it is the identification `K^∨(d)[2d] ⟶ 𝔻_X K` of blueprint
`theorem-poincare-duality--2`; it is an isomorphism for perfect `K`
(`AlgebraicGeometry.Etale.isIso_purityVerdierDualMap`). -/
noncomputable def purityVerdierDualMap (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)) (K : 𝐃(X, A)) :
    ((((derivedTensor A X).obj ((DerivedCategory.coefficientDual A X).obj (op K))).obj T)⟦
      (2 * d : ℤ)⟧) ⟶ ((RHom(X)[A]).flip.obj (G.obj (𝟙_ _))).obj (op K) :=
  MonoidalClosed.curry ((((derivedTensor A X).obj K).commShiftIso (2 * d : ℤ)).hom.app _ ≫
    (twistedEvaluation T K)⟦(2 * d : ℤ)⟧' ≫ γ.hom)

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] in
/-- Blueprint `theorem-poincare-duality--2` (the identification used by
`theorem-poincare-duality--7`): for a perfect `K`, the purity identification
`(K^∨ ⊗ᴸ T)[2d] ⟶ RHom(K, G Λ_Y)` is an isomorphism. -/
theorem isIso_purityVerdierDualMap (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)) {K : 𝐃(X, A)}
    (hK : IsDualizable K) : IsIso (purityVerdierDualMap γ K) := by
  refine isIso_of_bijective_comp_shift (2 * d : ℤ) _ fun W ↦ ?_
  have e : (fun g : W⟦(2 * d : ℤ)⟧ ⟶ _ ↦ g ≫ purityVerdierDualMap γ K) =
      MonoidalClosed.curry ∘
        (fun v ↦ (((derivedTensor A X).obj K).commShiftIso (2 * d : ℤ)).hom.app W ≫ v) ∘
          (fun z ↦ z ≫ γ.hom) ∘ (fun z ↦ z⟦(2 * d : ℤ)⟧') ∘
            (fun y ↦ ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) ∘
              (fun g ↦ (shiftFunctor _ (2 * d : ℤ)).preimage g) := by
    funext g
    simp only [Function.comp_apply, purityVerdierDualMap]
    refine (MonoidalClosed.curry_natural_left _ _).symm.trans ?_
    congr 1
    obtain ⟨y, rfl⟩ := (shiftFunctor (𝐃(X, A)) (2 * d : ℤ)).map_surjective g
    rw [Functor.preimage_map]
    change ((derivedTensor A X).obj K).map (y⟦(2 * d : ℤ)⟧') ≫ _ = _
    rw [Functor.commShiftIso_hom_naturality_assoc]
    simp
  rw [e]
  refine Function.Bijective.comp ⟨MonoidalClosed.curry_injective,
    fun g ↦ ⟨MonoidalClosed.uncurry g, MonoidalClosed.curry_uncurry g⟩⟩ ?_
  refine ((isIso_iff_coyoneda_map_bijective _).1 inferInstance _).comp ?_
  refine ((isIso_iff_yoneda_map_bijective _).1 inferInstance _).comp ?_
  refine Function.Bijective.comp ⟨(shiftFunctor _ _).map_injective,
    (shiftFunctor _ _).map_surjective⟩ ?_
  refine (bijective_derivedTensor_map_comp_twistedEvaluation A hK W).comp ?_
  exact ⟨fun g g' h ↦ by simpa using congrArg (shiftFunctor _ (2 * d : ℤ)).map h,
    fun y ↦ ⟨y⟦(2 * d : ℤ)⟧', by simp⟩⟩

end Purity

section Identification

variable {A} {d : ℕ} {T : 𝐃(X, A)} [IsIso (projectionMap A a)] {a}
  {G : 𝐃(Y, A) ⥤ 𝐃(X, A)} (adj : R(a)_![A] ⊣ G)

omit [HasSmallSiteSheafify A]

/-- Blueprint `theorem-poincare-duality--7`: Identification of the Poincaré pairing
with Verdier duality.

The tensor–internal-hom adjoint `β_K^♯ : (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨` of the derived
Poincaré pairing `β_K` (`AlgebraicGeometry.Etale.poincarePairing`) of a right adjoint `G` of
`Ra_!` and an isomorphism `γ : T[2d] ≅ G Λ_Y` (for finite coefficients, `G = Ra^!` and
`G Λ_Y = ω_X`) is the composite
```
(Ra_*(K^∨ ⊗ᴸ T))[2d] ≅ Ra_*((K^∨ ⊗ᴸ T)[2d]) --Ra_*(purity)--> Ra_* 𝔻_X K --(global duality)⁻¹-->
  (Ra_! K)^∨
```
of the purity identification (`AlgebraicGeometry.Etale.purityVerdierDualMap`) and the inverse of
the global Verdier-duality isomorphism
(`AlgebraicGeometry.Etale.globalVerdierDualityIsoOfAdjunction`).
Over `Y = Spec k` this is `RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨`. No hypothesis on `K` and no
properness of `a` is needed for this identity. -/
theorem curry_poincarePairing_eq (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)) (K : 𝐃(X, A)) :
    MonoidalClosed.curry (poincarePairing adj γ K) =
      ((R((a)_*[A])).commShiftIso (2 * d : ℤ)).inv.app _ ≫
        (R((a)_*[A])).map (purityVerdierDualMap γ K) ≫
          (globalVerdierDualityIsoOfAdjunction A adj K).inv := by
  refine (MonoidalClosed.curry_eq_iff _ _).2
    (Eq.symm ((MonoidalClosed.uncurry_natural_left _ _).trans ?_))
  erw [MonoidalClosed.uncurry_natural_left]
  rw [globalVerdierDualityIsoOfAdjunction_inv]
  erw [uncurry_derivedHomLowerShriekIsoOfAdjunction_hom_app_app]
  rw [exchangePairing]
  symm
  change _ = ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map _ ≫
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map _ ≫ _
  erw [reassoc_of% (mixedSupportCupProduct_naturality_right A a K (purityVerdierDualMap γ K))]
  have hu : ((derivedTensor A X).obj K).map (purityVerdierDualMap γ K) ≫
      (derivedTensorHomAdjunction A K).counit.app (G.obj (𝟙_ _)) =
      (((derivedTensor A X).obj K).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        (twistedEvaluation T K)⟦(2 * d : ℤ)⟧' ≫ γ.hom := by
    exact (MonoidalClosed.uncurry_eq _).symm.trans (MonoidalClosed.uncurry_curry _)
  have hu' : (R(a)_![A]).map (((derivedTensor A X).obj K).map (purityVerdierDualMap γ K)) ≫
      (R(a)_![A]).map ((derivedTensorHomAdjunction A K).counit.app (G.obj (𝟙_ _))) =
      (R(a)_![A]).map ((((derivedTensor A X).obj K).commShiftIso (2 * d : ℤ)).hom.app _) ≫
        (R(a)_![A]).map ((twistedEvaluation T K)⟦(2 * d : ℤ)⟧') ≫ (R(a)_![A]).map γ.hom := by
    refine (Functor.map_comp _ _ _).symm.trans ((congrArg (R(a)_![A]).map hu).trans ?_)
    simp only [Functor.map_comp]
  erw [reassoc_of% hu']
  rw [poincarePairing, poincarePairingEvaluation, smoothTrace]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_inv_naturality_assoc,
    reassoc_of% commShiftIso_hom_app_comp_mixedSupportCupProduct_shift]

/-- Blueprint `theorem-poincare-duality--7`: Identification of the Poincaré pairing
with Verdier duality.

For `K` perfect over `Λ_X`, the tensor–internal-hom adjoint
`β_K^♯ : (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨` of the derived Poincaré pairing is an isomorphism:
by `AlgebraicGeometry.Etale.curry_poincarePairing_eq` it is a composite of isomorphisms, the
purity identification being one by `AlgebraicGeometry.Etale.isIso_purityVerdierDualMap`. -/
theorem isIso_curry_poincarePairing (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)) {K : 𝐃(X, A)}
    (hK : IsDualizable K) : IsIso (MonoidalClosed.curry (poincarePairing adj γ K)) := by
  have := isIso_purityVerdierDualMap γ hK
  rw [curry_poincarePairing_eq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) (Iso.isIso_inv _))

/-- Blueprint `theorem-poincare-duality--7`: Identification of the Poincaré pairing
with Verdier duality.

For `K` perfect over `Λ_X`, the inverse of the isomorphism
`β_K^♯ : (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨`
(`AlgebraicGeometry.Etale.isIso_curry_poincarePairing`) is the global Verdier-duality
isomorphism `(Ra_! K)^∨ ≅ Ra_* 𝔻_X K`
(`AlgebraicGeometry.Etale.globalVerdierDualityIsoOfAdjunction`) followed by the inverse of the
smooth-purity identification `𝔻_X K ≅ (K^∨ ⊗ᴸ T)[2d]` and the shift compatibility of `Ra_*`.
Over `Y = Spec k` this is `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K) ≅ RΓ(X, K^∨(d))[2d]`. -/
theorem inv_curry_poincarePairing_eq (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)) {K : 𝐃(X, A)}
    (hK : IsDualizable K) :
    haveI := isIso_curry_poincarePairing adj γ hK
    haveI := isIso_purityVerdierDualMap γ hK
    inv (MonoidalClosed.curry (poincarePairing adj γ K)) =
      (globalVerdierDualityIsoOfAdjunction A adj K).hom ≫
        (R((a)_*[A])).map (inv (purityVerdierDualMap γ K)) ≫
          ((R((a)_*[A])).commShiftIso (2 * d : ℤ)).hom.app _ := by
  have := isIso_curry_poincarePairing adj γ hK
  have := isIso_purityVerdierDualMap γ hK
  refine IsIso.inv_eq_of_hom_inv_id ?_
  have hE := ((((R((a)_*[A])).commShiftIso (2 * d : ℤ)).app _).symm ≪≫
    (R((a)_*[A])).mapIso (asIso (purityVerdierDualMap γ K)) ≪≫
      (globalVerdierDualityIsoOfAdjunction A adj K).symm).hom_inv_id
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, asIso_hom, asIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc] at hE
  rw [curry_poincarePairing_eq]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_)
  exact hE

end Identification

end Etale

end AlgebraicGeometry
