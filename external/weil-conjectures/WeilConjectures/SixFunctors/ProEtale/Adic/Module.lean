/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.Ring

/-!
# Sheaves of modules over the constant `ℓ`-adic sheaf

Let `X` be a scheme and `ℚ̄_ℓ,X = AlgebraicGeometry.ProEtale.adicConstantSheaf ℓ X` the sheaf of
rings of locally finite continuous `ℓ`-adic functions on the pro-étale site of `X`. Following
Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8), the `ℓ`-adic sheaves on `X` are the
sheaves of `ℚ̄_ℓ,X`-modules: the module objects over the monoid `ℚ̄_ℓ,X` of the monoidal category
of sheaves of `ℚ̄_ℓ`-modules (`AlgebraicGeometry.ProEtale.AdicSheaf`). This is a Grothendieck
abelian category, in which kernels, cokernels and extensions are computed on the underlying
sheaves of `ℚ̄_ℓ`-modules; but its extensions are those of `ℚ̄_ℓ,X`-modules, not of sheaves of
modules over the discrete field `ℚ̄_ℓ`.

For a morphism `g : Z ⟶ Y` the pushforward `g_*` and the pullback `g^*` of sheaves of
`ℚ̄_ℓ`-modules lift to sheaves of modules over the constant `ℓ`-adic sheaves: `g_*` is lax
monoidal, so `g_* M` is a `g_* ℚ̄_ℓ,Z`-module, hence a `ℚ̄_ℓ,Y`-module along the ring morphism
`ℚ̄_ℓ,Y ⟶ g_* ℚ̄_ℓ,Z` (`AlgebraicGeometry.ProEtale.isMonHom_adicConstantSheafToLowerStar`); and
`g^*` is monoidal, so `g^* M` is a `g^* ℚ̄_ℓ,Y`-module, hence a `ℚ̄_ℓ,Z`-module along the ring
isomorphism `g^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,Z`. The underlying sheaves are those of the pushforward and the
pullback of sheaves of `ℚ̄_ℓ`-modules, so both functors are exact, and they are adjoint
(`AlgebraicGeometry.ProEtale.adicUpperStarLowerStarAdjunction`).

## Main definitions

- `AlgebraicGeometry.ProEtale.AdicSheaf`: sheaves of `ℚ̄_ℓ,X`-modules on `X_proét`.
- `AlgebraicGeometry.ProEtale.AdicSheaf.unit`: the constant `ℓ`-adic sheaf as a module over
  itself.
- `AlgebraicGeometry.ProEtale.adicLowerStar`, `AlgebraicGeometry.ProEtale.adicUpperStar`: `g_*`
  and `g^*`, with notations `(g)_*ᵃ[l]` and `(g)^*ᵃ[l]`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The sheaves of modules over the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` on the small pro-étale site
of `X` (Bhatt–Scholze, §6.8): module objects over the monoid `ℚ̄_ℓ,X` in the monoidal category of
sheaves of `ℚ̄_ℓ`-modules. -/
abbrev AdicSheaf (X : Scheme.{u}) : Type (u + 2) :=
  Mod (Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) (adicConstantSheaf l X)

variable {l}

namespace AdicSheaf

variable (l) in
/-- The constant `ℓ`-adic sheaf `ℚ̄_ℓ,X`, as a module over itself. -/
noncomputable abbrev unit (X : Scheme.{u}) : AdicSheaf l X :=
  Mod.regular (adicConstantSheaf l X)

/-- The underlying sheaf of `ℚ̄_ℓ`-modules of a sheaf of `ℚ̄_ℓ,X`-modules. -/
noncomputable abbrev forget (X : Scheme.{u}) :
    AdicSheaf l X ⥤ Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) :=
  Mod.forget _

noncomputable instance (X : Scheme.{u}) : Abelian (AdicSheaf l X) :=
  Mod.instAbelian _

instance (X : Scheme.{u}) : IsGrothendieckAbelian.{u + 1} (AdicSheaf l X) :=
  Mod.isGrothendieckAbelian _

end AdicSheaf

section Functors

open scoped Obj

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

noncomputable instance : IsIso (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).homEquiv
    _ _).symm (adicConstantSheafToLowerStar l g)) :=
  inferInstanceAs (IsIso (upperStarAdicConstantSheafHom l g))

instance : IsMonHom ((g)^*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l g)) :=
  inferInstance

instance : IsMonHom (show (g)^*[WeilCoefficients.{u} l].obj ((g)_*[WeilCoefficients.{u} l].obj
      (adicConstantSheaf l Z)) ⟶ adicConstantSheaf l Z from
    (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).counit.app
      (adicConstantSheaf l Z)) := by
  have h := NatTrans.isMonHom_app (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).counit
    (adicConstantSheaf l Z)
  constructor
  · dsimp only
    simpa only [Functor.obj.η_def, Functor.LaxMonoidal.comp_ε, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_ε, Functor.id_map,
      Category.id_comp] using h.one_hom
  · dsimp only
    simpa only [Functor.obj.μ_def, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_μ, Functor.id_map,
      Category.id_comp] using h.mul_hom

instance : IsMonHom (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).homEquiv
    _ _).symm (adicConstantSheafToLowerStar l g)) := by
  rw [Adjunction.homEquiv_counit]
  exact CategoryTheory.instIsMonHomComp _ (show (g)^*[WeilCoefficients.{u} l].obj
      ((g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l Z)) ⟶ adicConstantSheaf l Z from
    (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).counit.app
      (adicConstantSheaf l Z))

variable (l) in
/-- The pushforward `g_*` of sheaves of modules over the constant `ℓ`-adic sheaves: the
pushforward of the underlying sheaf, a module over `ℚ̄_ℓ,Y` along `ℚ̄_ℓ,Y ⟶ g_* ℚ̄_ℓ,Z`. -/
noncomputable def adicLowerStar : AdicSheaf l Z ⥤ AdicSheaf l Y :=
  (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).modRight
    (adicConstantSheafToLowerStar l g)

variable (l) in
/-- The pullback `g^*` of sheaves of modules over the constant `ℓ`-adic sheaves: the pullback of
the underlying sheaf, a module over `ℚ̄_ℓ,Z` along `g^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,Z`. -/
noncomputable def adicUpperStar : AdicSheaf l Y ⥤ AdicSheaf l Z :=
  (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).modLeft
    (adicConstantSheafToLowerStar l g)

@[inherit_doc adicLowerStar]
scoped notation "(" g ")_*ᵃ[" l "]" => adicLowerStar l g

@[inherit_doc adicUpperStar]
scoped notation "(" g ")^*ᵃ[" l "]" => adicUpperStar l g

variable (l) in
/-- The adjunction `g^* ⊣ g_*` on sheaves of modules over the constant `ℓ`-adic sheaves. -/
noncomputable def adicUpperStarLowerStarAdjunction : (g)^*ᵃ[l] ⊣ (g)_*ᵃ[l] :=
  (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).modAdjunction _

/-- The underlying sheaf of `g_* M` is the pushforward of the underlying sheaf of `M`. -/
lemma adicLowerStar_obj_X (M : AdicSheaf l Z) :
    ((g)_*ᵃ[l].obj M).X = (g)_*[WeilCoefficients.{u} l].obj M.X :=
  rfl

/-- The underlying sheaf of `g^* M` is the pullback of the underlying sheaf of `M`. -/
lemma adicUpperStar_obj_X (M : AdicSheaf l Y) :
    ((g)^*ᵃ[l].obj M).X = (g)^*[WeilCoefficients.{u} l].obj M.X :=
  rfl

lemma adicLowerStar_map_hom {M N : AdicSheaf l Z} (f : M ⟶ N) :
    ((g)_*ᵃ[l].map f).hom = (g)_*[WeilCoefficients.{u} l].map f.hom :=
  rfl

lemma adicUpperStar_map_hom {M N : AdicSheaf l Y} (f : M ⟶ N) :
    ((g)^*ᵃ[l].map f).hom = (g)^*[WeilCoefficients.{u} l].map f.hom :=
  rfl

instance : ((g)_*ᵃ[l]).Additive :=
  inferInstanceAs (Functor.mapMod _ _ ⋙ Mod.comap _).Additive

instance : ((g)^*ᵃ[l]).Additive :=
  inferInstanceAs (Functor.mapMod _ _ ⋙ Mod.comap _).Additive

instance : PreservesFiniteLimits (g)_*ᵃ[l] :=
  have : PreservesFiniteLimits ((g)_*ᵃ[l] ⋙ AdicSheaf.forget Y) :=
    inferInstanceAs (PreservesFiniteLimits (AdicSheaf.forget Z ⋙ (g)_*[WeilCoefficients.{u} l]))
  preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.forget Y)

instance : PreservesFiniteLimits (g)^*ᵃ[l] :=
  have : PreservesFiniteLimits ((g)^*ᵃ[l] ⋙ AdicSheaf.forget Z) :=
    inferInstanceAs (PreservesFiniteLimits (AdicSheaf.forget Y ⋙ (g)^*[WeilCoefficients.{u} l]))
  preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.forget Z)

instance : PreservesFiniteColimits (g)^*ᵃ[l] :=
  have : PreservesFiniteColimits ((g)^*ᵃ[l] ⋙ AdicSheaf.forget Z) :=
    inferInstanceAs
      (PreservesFiniteColimits (AdicSheaf.forget Y ⋙ (g)^*[WeilCoefficients.{u} l]))
  preservesFiniteColimits_of_reflects_of_preserves _ (AdicSheaf.forget Z)

end Functors

section Compat

variable (l)

/-- Pulling back functions along a composite is the composite of the pullbacks, up to the
composition isomorphism of pushforwards. -/
lemma adicConstantSheafToLowerStar_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    adicConstantSheafToLowerStar l h₂ ≫
        (h₂)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l h₁) ≫
          (lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).hom.app (adicConstantSheaf l T) =
      adicConstantSheafToLowerStar l (h₁ ≫ h₂) := by
  ext V : 3
  ext x
  refine adicConstantSheaf_ext (l := l) fun y ↦ ?_
  have key : ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h₁ h₂).hom.app
      V.unop).left ≫ pullback.fst _ h₁ ≫ pullback.fst V.unop.hom h₂ =
        pullback.fst V.unop.hom (h₁ ≫ h₂) := by
    simp only [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, NatIso.ofComponents_hom_app, MorphismProperty.Over.isoMk_hom_left]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.congrHom_hom]
    erw [pullback.map_id, Category.id_comp]
    exact pullbackLeftPullbackSndIso_inv_fst _ _ _
  exact congrArg (fun φ ↦ x.down.1 (φ.base y)) key

/-- Pulling back functions along the identity is the identity, up to the identification
`(𝟙 X)_* ≅ 𝟭`. -/
lemma adicConstantSheafToLowerStar_id (X : Scheme.{u}) :
    adicConstantSheafToLowerStar l (𝟙 X) ≫
        (lowerStarId (WeilCoefficients.{u} l) X).hom.app (adicConstantSheaf l X) = 𝟙 _ := by
  ext V : 3
  ext x
  refine adicConstantSheaf_ext (l := l) fun y ↦ ?_
  have key : ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).left ≫
      pullback.fst V.unop.hom (𝟙 X) = 𝟙 _ := by
    simp [MorphismProperty.Over.pullbackId]
  exact congrArg (fun φ ↦ x.down.1 (φ.base y)) key

end Compat

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime]

section Isos

instance {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    NatTrans.IsMonoidal (lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h₁ h₂).symm)
    (WeilCoefficients.{u} l) (Scheme.ProEt.topology R) (Scheme.ProEt.topology S)
    (Scheme.ProEt.topology T)).hom)

instance (X : Scheme.{u}) : NatTrans.IsMonoidal (lowerStarId (WeilCoefficients.{u} l) X).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) (WeilCoefficients.{u} l)
    (Scheme.ProEt.topology X)).hom)

variable (l) in
/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of sheaves of modules over the
constant `ℓ`-adic sheaves: that of the underlying sheaves, which is linear. -/
noncomputable def adicLowerStarComp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    (h₁)_*ᵃ[l] ⋙ (h₂)_*ᵃ[l] ≅ (h₁ ≫ h₂)_*ᵃ[l] :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk ((lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).app M.X)
      (Functor.act_comp_app_of_isMonoidal (lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).hom
        (adicConstantSheafToLowerStar l h₁) (adicConstantSheafToLowerStar l h₂)
        (adicConstantSheafToLowerStar l (h₁ ≫ h₂)) (adicConstantSheafToLowerStar_comp l h₁ h₂) M))
    fun f ↦ Mod.hom_ext _ _ ((lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).hom.naturality f.hom)

variable (l) in
/-- The identity isomorphism `(𝟙 X)_* ≅ 𝟭` of sheaves of modules over the constant `ℓ`-adic
sheaf. -/
noncomputable def adicLowerStarId (X : Scheme.{u}) : (𝟙 X)_*ᵃ[l] ≅ 𝟭 (AdicSheaf l X) :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk (M := (𝟙 X)_*ᵃ[l].obj M) (N := (Mod.comap (D := Sheaf _ _)
        (𝟙 (adicConstantSheaf l X))).obj M) ((lowerStarId (WeilCoefficients.{u} l) X).app M.X)
      (Functor.act_comp_app_of_isMonoidal_id (lowerStarId (WeilCoefficients.{u} l) X).hom
        (adicConstantSheafToLowerStar l (𝟙 X)) (𝟙 _)
        (adicConstantSheafToLowerStar_id l X) M))
    (fun f ↦ Mod.hom_ext _ _ ((lowerStarId (WeilCoefficients.{u} l) X).hom.naturality f.hom)) ≪≫
  Mod.comapId _

variable (l) in
/-- The pushforwards of sheaves of modules along equal morphisms are isomorphic. -/
noncomputable def adicLowerStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)_*ᵃ[l] ≅ (g')_*ᵃ[l] :=
  NatIso.ofComponents (fun M ↦ Mod.isoMk (M := (g)_*ᵃ[l].obj M) (N := (g')_*ᵃ[l].obj M)
      ((lowerStarCongr (WeilCoefficients.{u} l) h).app M.X) (by
        subst h
        simp only [lowerStarCongr_rfl, Iso.app_hom, Iso.refl_hom, NatTrans.id_app]
        erw [Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]))
    fun f ↦ Mod.hom_ext _ _ ((lowerStarCongr (WeilCoefficients.{u} l) h).hom.naturality f.hom)

lemma adicLowerStarCongr_hom_app_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (M : AdicSheaf l Z) :
    ((adicLowerStarCongr l h).hom.app M).hom =
      (lowerStarCongr (WeilCoefficients.{u} l) h).hom.app M.X :=
  rfl

lemma adicLowerStarComp_hom_app_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : AdicSheaf l T) :
    ((adicLowerStarComp l h₁ h₂).hom.app M).hom =
      (lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).hom.app M.X :=
  rfl

lemma adicLowerStarComp_inv_app_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : AdicSheaf l T) :
    ((adicLowerStarComp l h₁ h₂).inv.app M).hom =
      (lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).inv.app M.X :=
  rfl

variable (l) in
/-- The pullbacks of sheaves of modules along equal morphisms are isomorphic. -/
noncomputable def adicUpperStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)^*ᵃ[l] ≅ (g')^*ᵃ[l] :=
  eqToIso (by rw [h])

variable (l) in
/-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭` of sheaves of modules over the constant `ℓ`-adic
sheaf, by uniqueness of left adjoints. -/
noncomputable def adicUpperStarId (X : Scheme.{u}) : (𝟙 X)^*ᵃ[l] ≅ 𝟭 (AdicSheaf l X) :=
  (conjugateIsoEquiv Adjunction.id (adicUpperStarLowerStarAdjunction l (𝟙 X))).symm
    (adicLowerStarId l X).symm

variable (l) in
/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of sheaves of modules over the
constant `ℓ`-adic sheaves, by uniqueness of left adjoints. -/
noncomputable def adicUpperStarComp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    (h₁ ≫ h₂)^*ᵃ[l] ≅ (h₂)^*ᵃ[l] ⋙ (h₁)^*ᵃ[l] :=
  ((conjugateIsoEquiv (adicUpperStarLowerStarAdjunction l (h₁ ≫ h₂))
      ((adicUpperStarLowerStarAdjunction l h₂).comp (adicUpperStarLowerStarAdjunction l h₁))).symm
    (adicLowerStarComp l h₁ h₂).symm).symm

variable (l) in
/-- The pullbacks along the two sides of a commutative square agree. -/
noncomputable def adicUpperStarCompIso {Y Z₁ Z₂ T : Scheme.{u}} {a : Y ⟶ Z₁} {b : Z₁ ⟶ T}
    {c : Y ⟶ Z₂} {d : Z₂ ⟶ T} (h : a ≫ b = c ≫ d) :
    (b)^*ᵃ[l] ⋙ (a)^*ᵃ[l] ≅ (d)^*ᵃ[l] ⋙ (c)^*ᵃ[l] :=
  (adicUpperStarComp l a b).symm ≪≫ adicUpperStarCongr l h ≪≫ adicUpperStarComp l c d

variable (l) in
/-- The congruence isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_adicUpperStarCongr_inv {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g') :
    conjugateEquiv (adicUpperStarLowerStarAdjunction l g) (adicUpperStarLowerStarAdjunction l g')
      (adicUpperStarCongr l h).inv = (adicLowerStarCongr l h).hom := by
  subst h
  refine NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_)
  simp [adicUpperStarCongr, adicLowerStarCongr_hom_app_hom]
  rfl

variable (l) in
/-- The inverse of the composition isomorphism of pullbacks is conjugate to that of
pushforwards. -/
lemma conjugateEquiv_adicUpperStarComp_inv {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateEquiv (adicUpperStarLowerStarAdjunction l (h₁ ≫ h₂))
      ((adicUpperStarLowerStarAdjunction l h₂).comp (adicUpperStarLowerStarAdjunction l h₁))
      (adicUpperStarComp l h₁ h₂).inv = (adicLowerStarComp l h₁ h₂).inv :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (adicLowerStarComp l h₁ h₂).symm)

variable (l) in
/-- The composition isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_adicUpperStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateEquiv ((adicUpperStarLowerStarAdjunction l h₂).comp
        (adicUpperStarLowerStarAdjunction l h₁))
      (adicUpperStarLowerStarAdjunction l (h₁ ≫ h₂)) (adicUpperStarComp l h₁ h₂).hom =
        (adicLowerStarComp l h₁ h₂).hom := by
  have := conjugateEquiv_comm (adicUpperStarLowerStarAdjunction l (h₁ ≫ h₂))
    ((adicUpperStarLowerStarAdjunction l h₂).comp (adicUpperStarLowerStarAdjunction l h₁))
    (α := (adicUpperStarComp l h₁ h₂).inv) (β := (adicUpperStarComp l h₁ h₂).hom) (by simp)
  rw [conjugateEquiv_adicUpperStarComp_inv] at this
  rw [← cancel_epi (adicLowerStarComp l h₁ h₂).inv, this, Iso.inv_hom_id]

variable (l) in
/-- **The pullback of the constant `ℓ`-adic sheaf is the constant `ℓ`-adic sheaf**, as sheaves
of modules over the constant `ℓ`-adic sheaf: `g^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,Z`
(`AlgebraicGeometry.ProEtale.upperStarAdicConstantSheafIso`, a ring isomorphism). -/
noncomputable def adicUpperStarUnitIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (g)^*ᵃ[l].obj (AdicSheaf.unit l Y) ≅ AdicSheaf.unit l Z :=
  Mod.regularIsoOfIsIso _

variable (l) in
/-- **The pushforward of the constant `ℓ`-adic sheaf along an isomorphism** `e : X ≅ Y` is the
constant `ℓ`-adic sheaf, as sheaves of modules: the inverse of the ring isomorphism
`ℚ̄_ℓ,Y ⟶ e_* ℚ̄_ℓ,X`, whose underlying morphism is
`AlgebraicGeometry.ProEtale.adicConstantSheafLowerStarIso`. -/
noncomputable def adicLowerStarUnitIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (e.hom)_*ᵃ[l].obj (AdicSheaf.unit l X) ≅ AdicSheaf.unit l Y :=
  Mod.isoMk (M := (e.hom)_*ᵃ[l].obj (AdicSheaf.unit l X)) (N := AdicSheaf.unit l Y)
    (adicConstantSheafLowerStarIso l e) (by
      have : IsMonHom (adicConstantSheafLowerStarIso l e).inv :=
        inferInstanceAs (IsMonHom (adicConstantSheafToLowerStar l e.hom))
      have : IsMonHom (adicConstantSheafLowerStarIso l e).hom := by
        have : IsMonHom (inv (adicConstantSheafLowerStarIso l e).inv) := inferInstance
        rwa [IsIso.Iso.inv_inv] at this
      have h := IsMonHom.mul_hom (f := (adicConstantSheafLowerStarIso l e).hom)
      change ((adicConstantSheafLowerStarIso l e).inv ▷ _ ≫ μ) ≫ _ = _
      rw [Category.assoc, h, tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc,
        Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
      rfl)

lemma adicLowerStarUnitIso_hom_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    (adicLowerStarUnitIso l e).hom.hom = (adicConstantSheafLowerStarIso l e).hom :=
  rfl

end Isos

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- Multiplication by a scalar `c ∈ ℚ̄_ℓ`, an endomorphism of a sheaf of `ℚ̄_ℓ,X`-modules. -/
noncomputable def smul (c : ULift.{u + 1} (PadicAlgCl l)) (M : AdicSheaf l X) : M ⟶ M :=
  Mod.homMk (c • 𝟙 M.X) (by
    rw [Linear.comp_smul, Category.comp_id, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])

@[simp]
lemma smul_hom (c : ULift.{u + 1} (PadicAlgCl l)) (M : AdicSheaf l X) :
    (smul c M).hom = c • 𝟙 M.X :=
  rfl

lemma smul_comp (c : ULift.{u + 1} (PadicAlgCl l)) {M N : AdicSheaf l X} (f : M ⟶ N) :
    smul c M ≫ f = f ≫ smul c N :=
  Mod.hom_ext _ _ (by simp)

lemma smul_smul (c d : ULift.{u + 1} (PadicAlgCl l)) (M : AdicSheaf l X) :
    smul c M ≫ smul d M = smul (d * c) M :=
  Mod.hom_ext _ _ (by simp [_root_.smul_smul])

lemma smul_one (M : AdicSheaf l X) : smul 1 M = 𝟙 M :=
  Mod.hom_ext _ _ (by simp)

/-- The pushforward commutes with multiplication by a scalar. -/
lemma adicLowerStar_map_smul {Z : Scheme.{u}} (g : X ⟶ Z) (c : ULift.{u + 1} (PadicAlgCl l))
    (M : AdicSheaf l X) : (g)_*ᵃ[l].map (smul c M) = smul c ((g)_*ᵃ[l].obj M) :=
  Mod.hom_ext _ _ (by ext : 3; rfl)

end AlgebraicGeometry.ProEtale.AdicSheaf
