/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.CokernelNSMul
public import WeilConjectures.Mathlib.Algebra.GroupWithZero.Basic
public import WeilConjectures.TateTwist.RootsOfUnityUpperStar
public import WeilConjectures.TateTwist.TateModuleTrivialization
public import WeilConjectures.TateTwist.UpperStarExtendScalars

/-!
# Pullback of the Tate module along an arbitrary morphism

Let `g : X' ⟶ X` be a morphism of schemes, with `X` over a field `k` in which the prime `ℓ` is
invertible. The pullback of module objects along `g` sends the Tate twist
`ℚ̄_ℓ,X(1) = ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} lim_n (ℤ_ℓ,X ⊗ μ_{ℓⁿ})` to `ℚ̄_ℓ,X'(1)`
(`AlgebraicGeometry.ProEtale.upperStarTateTwistOneIso`):

* the pullback of a free module is the free module on the pullback
  (`AlgebraicGeometry.ProEtale.CondensedRing.freeFunctorCompUpperStarIso`), so the pullback of a
  tower of free modules `n ↦ Λ_X ⊗ Fₙ` is the tower `n ↦ Λ_X' ⊗ F'ₙ` as soon as `g^* Fₙ ≅ F'ₙ`
  compatibly with the transition maps (`AlgebraicGeometry.ProEtale.upperStarFreeTowerIso`); for
  the Tate module tower, `g^* μ_{ℓⁿ} ≅ μ_{ℓⁿ}` compatibly with the power maps
  (`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIsoOfInvertible`);
* the pullback commutes with the limit of the Tate module tower
  (`AlgebraicGeometry.ProEtale.preservesLimit_upperStar_tateModuleSystem`). This is not formal,
  `g^*` not commuting with sequential limits in general. It is checked after the pro-étale cover
  `X' ×_k Spec kˢᵉᵖ ⟶ X'`, through which `g` factors as `X' ×_k kˢᵉᵖ ⟶ X ×_k kˢᵉᵖ ⟶ X`: over
  `X ×_k kˢᵉᵖ` the tower becomes the tower `n ↦ ℤ_ℓ / ℓⁿ` of reductions of the `ℓ`-adically
  complete `ℤ_ℓ` (`AlgebraicGeometry.ProEtale.upperStarTateModuleSystemIso`), whose limit is
  preserved by every pullback, since pullbacks preserve cokernels and send `ℤ_ℓ` to `ℤ_ℓ`
  (`AlgebraicGeometry.ProEtale.preservesLimit_upperStar_of_isColimitCokernelCofork`);
* the pullback commutes with the extension of scalars along `ℤ_ℓ ⟶ ℚ̄_ℓ`
  (`AlgebraicGeometry.ProEtale.CondensedRing.pullIso`).

## Implementation notes

The constructions are stated for an arbitrary commutative condensed ring `Λ` and towers of free
modules (`AlgebraicGeometry.ProEtale.upperStarExtendScalarsLimitFreeTowerIso`), and only
specialized to `Λ = ℤ_ℓ` in `AlgebraicGeometry.ProEtale.upperStarTateTwistOneIso`, whose type only
involves `ℚ̄_ℓ`-modules. Stating isomorphisms between pullbacks of module objects over the
concrete ring `C(-, ℤ_ℓ)` (`Profinite.continuousMapRingObj ℤ_[ℓ]`) directly makes the kernel time
out when checking the instances of the categories of module objects.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### Pullbacks preserve limits of towers of reductions of `ℤ_ℓ` -/

/-- Let `c` be a cone over a tower of abelian sheaves on `Y_proét` whose legs `c.pt ⟶ Fₙ` are
cokernels of `ℓⁿ` and whose point is isomorphic to `ℤ_ℓ,Y`. Then every pullback `h^*` preserves
the limit of the tower: `h^*` preserves cokernels and `h^* ℤ_ℓ,Y ≅ ℤ_ℓ,Y'` is `ℓ`-adically
complete. -/
lemma preservesLimit_upperStar_of_isColimitCokernelCofork {Y Y' : Scheme.{u}} (h : Y' ⟶ Y)
    (ℓ : ℕ) [Fact ℓ.Prime] {F : ℕᵒᵖ ⥤ Sheaf (ProEt.topology Y) Ab.{u + 1}} (c : Cone F)
    (w : ∀ n : ℕ, (((ℓ ^ n : ℕ) : ℤ) • 𝟙 c.pt) ≫ c.π.app (op n) = 0)
    (hc : ∀ n : ℕ, IsColimit (CokernelCofork.ofπ _ (w n)))
    (e : c.pt ≅ condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) Y) :
    PreservesLimit F (h)^*[Ab.{u + 1}] := by
  have w' (n : ℕ) : (((ℓ ^ n : ℕ) : ℤ) • 𝟙 ((h)^*[Ab.{u + 1}].obj c.pt)) ≫
      (h)^*[Ab.{u + 1}].map (c.π.app (op n)) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, ← Functor.map_comp, w n,
      Functor.map_zero]
  refine preservesLimit_of_preserves_limit_cone
    (isLimitOfIsColimitCokernelCofork c w hc
      (isLimitCokernelPowTowerConeOfIso e.symm (isLimitCokernelPowTowerCone ℓ Y)))
    (isLimitOfIsColimitCokernelCofork ((h)^*[Ab.{u + 1}].mapCone c) w' (fun n ↦ ?_)
      (isLimitCokernelPowTowerConeOfIso
        (((upperStarFromPointComp h).app (Profinite.continuousMapRingObj ℤ_[ℓ])).symm ≪≫
          (h)^*[Ab.{u + 1}].mapIso e.symm) (isLimitCokernelPowTowerCone ℓ Y')))
  refine CokernelCofork.isColimitOfEq ?_
    (isColimitCoforkMapOfIsColimit' (h)^*[Ab.{u + 1}] (w n) (hc n))
  rw [Functor.map_zsmul, CategoryTheory.Functor.map_id]
  rfl

/-! ### Pullbacks of free modules -/

/-- **The pullback of a free module is the free module on the pullback**: `f^*(Λ_Y ⊗ M) ≅
Λ_X ⊗ f^* M`. Both functors are left adjoint to `N ↦ f_* N`, viewed as an abelian sheaf. -/
noncomputable def CondensedRing.freeFunctorCompUpperStarIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod.freeFunctor (condensedRingObj Λ Y) ⋙ CondensedRing.upperStar Λ f ≅
      (f)^*[Ab.{u + 1}] ⋙ Mod.freeFunctor (condensedRingObj Λ X) :=
  (conjugateIsoEquiv ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).comp
      (Mod.freeForgetAdjunction _))
    ((Mod.freeForgetAdjunction _).comp (CondensedRing.upperStarLowerStarAdjunction Λ f))).symm
    (Iso.refl _)

/-! ### Pullback of limits of towers of free modules -/

section FreeTower

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- If the pullback `g^*` of abelian sheaves preserves the limit of the underlying diagram, then
the pullback of module objects over `Λ` preserves the limit of the diagram: the pullback of module
objects is `mapMod(g^*)`, whose limits are computed on underlying objects, followed by the
extension of scalars along the isomorphism `α_g`, an equivalence. -/
lemma CondensedRing.preservesLimit_upperStar
    (K : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    [PreservesLimit (K ⋙ Mod.forget _) (g)^*[Ab.{u + 1}]] :
    PreservesLimit K (CondensedRing.upperStar Λ g) := by
  have : PreservesLimit K ((g)^*[Ab.{u + 1}].mapMod _ ⋙ Mod.forget _) :=
    inferInstanceAs (PreservesLimit _ (Mod.forget _ ⋙ (g)^*[Ab.{u + 1}]))
  have : PreservesLimit K ((g)^*[Ab.{u + 1}].mapMod _) :=
    preservesLimit_of_reflects_of_preserves _ (Mod.forget _)
  exact inferInstanceAs (PreservesLimit _ ((g)^*[Ab.{u + 1}].mapMod _ ⋙ Mod.extendScalars _))

variable {F : ℕ → Sheaf (ProEt.topology X) Ab.{u + 1}} (t : ∀ n, F (n + 1) ⟶ F n)
  {F' : ℕ → Sheaf (ProEt.topology X') Ab.{u + 1}} (t' : ∀ n, F' (n + 1) ⟶ F' n)
  (e : ∀ n, (g)^*[Ab.{u + 1}].obj (F n) ≅ F' n)

/-- The components `g^*(Λ_X ⊗ Fₙ) ≅ Λ_X' ⊗ F'ₙ` of the pullback of a tower of free modules. -/
noncomputable def upperStarFreeTowerIsoApp (n : ℕ) :
    (CondensedRing.upperStar Λ g).obj ((Mod.freeFunctor (condensedRingObj Λ X)).obj (F n)) ≅
      (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n) :=
  (CondensedRing.freeFunctorCompUpperStarIso Λ g).app (F n) ≪≫
    (Mod.freeFunctor (condensedRingObj Λ X')).mapIso (e n)

variable {t t' e} in
lemma upperStarFreeTowerIsoApp_naturality
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n) (n : ℕ) :
    (CondensedRing.upperStar Λ g).map ((Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ≫
        (upperStarFreeTowerIsoApp Λ g e n).hom =
      (upperStarFreeTowerIsoApp Λ g e (n + 1)).hom ≫
        (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n) := by
  have h := (CondensedRing.freeFunctorCompUpperStarIso Λ g).hom.naturality (t n)
  rw [Functor.comp_map, Functor.comp_map] at h
  rw [upperStarFreeTowerIsoApp, upperStarFreeTowerIsoApp, Iso.trans_hom, Iso.trans_hom,
    Iso.app_hom, Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_hom, reassoc_of% h,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp, he]

/-- The comparison from the pullback of the tower of free modules `n ↦ Λ_X ⊗ Fₙ` to the tower of
free modules `n ↦ Λ_X' ⊗ F'ₙ`, given compatible isomorphisms `g^* Fₙ ≅ F'ₙ`. -/
noncomputable def upperStarFreeTowerHom
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n) :
    Functor.ofOpSequence (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ⋙
        CondensedRing.upperStar Λ g ⟶
      Functor.ofOpSequence (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n)) :=
  NatTrans.ofOpSequence (fun n ↦ (upperStarFreeTowerIsoApp Λ g e n).hom) (fun n ↦ by
    simpa using upperStarFreeTowerIsoApp_naturality Λ g he n)

instance (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n) :
    IsIso (upperStarFreeTowerHom Λ g t t' e he) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  exact inferInstanceAs (IsIso (upperStarFreeTowerIsoApp Λ g e n.unop).hom)

/-- The pullback of the tower of free modules `n ↦ Λ_X ⊗ Fₙ` is the tower of free modules
`n ↦ Λ_X' ⊗ F'ₙ`, given compatible isomorphisms `g^* Fₙ ≅ F'ₙ`. -/
noncomputable def upperStarFreeTowerIso
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n) :
    Functor.ofOpSequence (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ⋙
        CondensedRing.upperStar Λ g ≅
      Functor.ofOpSequence (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n)) :=
  asIso (upperStarFreeTowerHom Λ g t t' e he)

/-- **The pullback of the limit of a tower of free modules**: if `g^*` preserves the limit of
the tower `n ↦ Λ_X ⊗ Fₙ` of abelian sheaves, then `g^* lim_n (Λ_X ⊗ Fₙ) ≅ lim_n (Λ_X' ⊗ F'ₙ)`,
given compatible isomorphisms `g^* Fₙ ≅ F'ₙ`. -/
noncomputable def upperStarLimitFreeTowerIso
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n)
    (hK : PreservesLimit (Functor.ofOpSequence
      (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
      (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ⋙ Mod.forget _)
      (g)^*[Ab.{u + 1}]) :
    (CondensedRing.upperStar Λ g).obj (limit (Functor.ofOpSequence
      (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
      (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)))) ≅
      limit (Functor.ofOpSequence
        (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n))) :=
  have := hK
  have := CondensedRing.preservesLimit_upperStar Λ g (Functor.ofOpSequence
    (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
    (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)))
  preservesLimitIso _ _ ≪≫ HasLimit.isoOfNatIso (upperStarFreeTowerIso Λ g t t' e he)

/-- **The pullback of the extension of scalars of the limit of a tower of free modules**: for a
morphism `a : Λ ⟶ Λ'` of commutative condensed rings, if `g^*` preserves the limit of the tower
`n ↦ Λ_X ⊗ Fₙ` of abelian sheaves, then `g^*(Λ'_X ⊗_{Λ_X} lim_n (Λ_X ⊗ Fₙ)) ≅
Λ'_X' ⊗_{Λ_X'} lim_n (Λ_X' ⊗ F'ₙ)`, given compatible isomorphisms `g^* Fₙ ≅ F'ₙ`. -/
noncomputable def upperStarExtendScalarsLimitFreeTowerIso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n)
    (hK : PreservesLimit (Functor.ofOpSequence
      (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
      (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ⋙ Mod.forget _)
      (g)^*[Ab.{u + 1}]) :
    (CondensedRing.upperStar Λ' g).obj ((Mod.extendScalars (coefficientMap a X)).obj
      (limit (Functor.ofOpSequence
        (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n))))) ≅
      (Mod.extendScalars (coefficientMap a X')).obj (limit (Functor.ofOpSequence
        (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n)))) :=
  ((CondensedRing.pullIso a g).app _).symm ≪≫
    (Mod.extendScalars (coefficientMap a X')).mapIso (upperStarLimitFreeTowerIso Λ g t t' e he hK)

end FreeTower

/-! ### The Tate module and `ℚ̄_ℓ(1)` -/

section Invertible

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : k)] {X X' : Scheme.{u}}
  (g : X' ⟶ X)

omit [Fact ℓ.Prime] [NeZero (ℓ : k)] in
/-- The pullback along the pro-étale cover `X ×_k Spec kˢᵉᵖ ⟶ X` reflects isomorphisms. -/
lemma reflectsIsomorphisms_upperStar_pullbackFstSpecSepClosureHom (f : X ⟶ Spec (.of k)) :
    (pullback.fst f (specSepClosureHom k))^*[Ab.{u + 1}].ReflectsIsomorphisms := by
  let 𝒰 := sepClosureCover f
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  refine ⟨fun φ hφ ↦ isIso_of_isIso_localizationRestriction Ab.{u + 1} _ 𝒰.f 𝒰.mem₀ fun i ↦ ?_⟩
  exact (NatIso.isIso_map_iff
    (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) inferInstance) _).1 hφ

/-- **The pullback commutes with the limit of the Tate module tower.** For `g : X' ⟶ X` with `X`
over a field in which `ℓ` is invertible, `g^*` preserves the limit `ℤ_ℓ(1) = lim_n μ_{ℓⁿ}`. -/
theorem preservesLimit_upperStar_tateModuleSystem (f : X ⟶ Spec (.of k)) :
    PreservesLimit (tateModuleSystem X ℓ ⋙ Mod.forget _) (g)^*[Ab.{u + 1}] := by
  have : NeZero (ℓ : SeparableClosure k) :=
    ‹NeZero (ℓ : k)›.of_injective (algebraMap k (SeparableClosure k)).injective
  obtain ⟨ζ, hζ, hζ'⟩ := IsSepClosed.exists_isPrimitiveRoot_pow_eq (SeparableClosure k) ℓ
  let w := pullback.fst f (specSepClosureHom k)
  let w' := pullback.fst (g ≫ f) (specSepClosureHom k)
  let a : pullback (g ≫ f) (specSepClosureHom k) ⟶ pullback f (specSepClosureHom k) :=
    pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (by simp) (by simp)
  have ha : a ≫ w = w' ≫ g := pullback.lift_fst _ _ _
  let B := (w)^*[Ab.{u + 1}].obj (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)
  have : PreservesLimit ((tateModuleSystem X ℓ ⋙ Mod.forget _) ⋙ (w)^*[Ab.{u + 1}])
      (a)^*[Ab.{u + 1}] := by
    have := preservesLimit_upperStar_of_isColimitCokernelCofork a ℓ
      ((Mod.forget B).mapCone (Mod.freeCokernelPowTowerCone B ℓ)) _
      (fun n ↦ Mod.isColimitCokernelCoforkFreeCokernelPowTowerCone B ℓ n)
      ((upperStarFromPointComp w).app _)
    exact preservesLimit_of_iso_diagram _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerRight (upperStarTateModuleSystemIso w (pullback.snd f _) ℓ hζ hζ')
        (Mod.forget B)).symm
  have : PreservesLimit (tateModuleSystem X ℓ ⋙ Mod.forget _)
      ((g)^*[Ab.{u + 1}] ⋙ (w')^*[Ab.{u + 1}]) :=
    preservesLimit_of_natIso _ ((upperStarComp Ab.{u + 1} a w).symm ≪≫
      eqToIso (congrArg (upperStar Ab.{u + 1}) ha) ≪≫ upperStarComp Ab.{u + 1} w' g)
  have := reflectsIsomorphisms_upperStar_pullbackFstSpecSepClosureHom (g ≫ f)
  have : ReflectsLimit ((tateModuleSystem X ℓ ⋙ Mod.forget _) ⋙ (g)^*[Ab.{u + 1}])
      (w')^*[Ab.{u + 1}] := reflectsLimit_of_reflectsIsomorphisms _ _
  exact preservesLimit_of_reflects_of_preserves _ (w')^*[Ab.{u + 1}]

omit [Field k] in
@[reassoc]
lemma upperStar_map_eqToHom_comp_upperStarRootsOfUnitySheafHom {N N' : ℕ} (h : N = N') :
    (g)^*[Ab.{u + 1}].map (eqToHom (congrArg (rootsOfUnitySheaf X) h)) ≫
        upperStarRootsOfUnitySheafHom g N' =
      upperStarRootsOfUnitySheafHom g N ≫ eqToHom (congrArg (rootsOfUnitySheaf X') h) := by
  subst h
  simp

omit [Field k] [Fact ℓ.Prime] in
/-- The comparison maps `g^* μ_{ℓⁿ} ⟶ μ_{ℓⁿ}` are compatible with the transition maps of the
Tate module towers. -/
lemma upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom (n : ℕ) :
    (g)^*[Ab.{u + 1}].map (eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ n)) ≫
        rootsOfUnitySheafPow X (ℓ ^ n) ℓ) ≫ upperStarRootsOfUnitySheafHom g (ℓ ^ n) =
      upperStarRootsOfUnitySheafHom g (ℓ ^ (n + 1)) ≫
        eqToHom (congrArg (rootsOfUnitySheaf X') (pow_succ' ℓ n)) ≫
          rootsOfUnitySheafPow X' (ℓ ^ n) ℓ := by
  rw [Functor.map_comp, Category.assoc,
    upperStar_map_rootsOfUnitySheafPow_comp_upperStarRootsOfUnitySheafHom,
    upperStar_map_eqToHom_comp_upperStarRootsOfUnitySheafHom_assoc g (pow_succ' ℓ n)]

/-- **The pullback of `ℚ̄_ℓ(1)` is `ℚ̄_ℓ(1)`**: `g^* ℚ̄_ℓ,X(1) ≅ ℚ̄_ℓ,X'(1)` as
`ℚ̄_ℓ,X'`-modules, for `g : X' ⟶ X` with `X` over a field `k` in which `ℓ` is invertible. The
pullback commutes with the extension of scalars along `ℤ_ℓ ⟶ ℚ̄_ℓ`, with the limit of the Tate
module tower (`AlgebraicGeometry.ProEtale.preservesLimit_upperStar_tateModuleSystem`) and with
free modules, and `g^* μ_{ℓⁿ} ≅ μ_{ℓⁿ}`
(`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIsoOfInvertible`). -/
noncomputable def upperStarTateTwistOneIso (f : X ⟶ Spec (.of k)) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).obj (tateTwistOne X ℓ) ≅
      tateTwistOne X' ℓ :=
  upperStarExtendScalarsLimitFreeTowerIso (Profinite.continuousMapRingObj ℤ_[ℓ]) g
    (F := fun n ↦ rootsOfUnitySheaf X (ℓ ^ n)) (F' := fun n ↦ rootsOfUnitySheaf X' (ℓ ^ n))
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X (ℓ ^ n) ℓ)
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X') (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X' (ℓ ^ n) ℓ)
    (fun n ↦ have := NeZero.natCast_pow (R := k) ℓ n
      upperStarRootsOfUnitySheafIsoOfInvertible g f (ℓ ^ n))
    (Profinite.padicIntRingObjToPadicAlgCl ℓ)
    (upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom ℓ g)
    (preservesLimit_upperStar_tateModuleSystem ℓ g f)

end Invertible

end AlgebraicGeometry.ProEtale
