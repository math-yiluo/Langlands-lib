/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Ring

/-!
# Sheaves of modules over the constant sheaf

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Module`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

Let `X` be a scheme and `Λ_X = AlgebraicGeometry.ProEtale.fieldConstantSheaf Λ X` the sheaf of
rings of continuous `Λ`-valued functions on the pro-étale site of `X`. Following
Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8), the `Λ`-adic sheaves on `X` are the
sheaves of `Λ_X`-modules: the module objects over the monoid `Λ_X` of the monoidal category
of sheaves of `Λ`-modules (`AlgebraicGeometry.ProEtale.FieldSheaf`). This is a Grothendieck
abelian category, in which kernels, cokernels and extensions are computed on the underlying
sheaves of `Λ`-modules; but its extensions are those of `Λ_X`-modules, not of sheaves of
modules over the discrete field `Λ`.

For a morphism `g : Z ⟶ Y` the pushforward `g_*` and the pullback `g^*` of sheaves of
`Λ`-modules lift to sheaves of modules over the constant sheaves `Λ_X`: `g_*` is lax
monoidal, so `g_* M` is a `g_* Λ_Z`-module, hence a `Λ_Y`-module along the ring morphism
`Λ_Y ⟶ g_* Λ_Z` (`AlgebraicGeometry.ProEtale.isMonHom_fieldConstantSheafToLowerStar`); and
`g^*` is monoidal, so `g^* M` is a `g^* Λ_Y`-module, hence a `Λ_Z`-module along the ring
isomorphism `g^* Λ_Y ≅ Λ_Z`. The underlying sheaves are those of the pushforward and the
pullback of sheaves of `Λ`-modules, so both functors are exact, and they are adjoint
(`AlgebraicGeometry.ProEtale.fieldUpperStarLowerStarAdjunction`).

## Main definitions

- `AlgebraicGeometry.ProEtale.FieldSheaf`: sheaves of `Λ_X`-modules on `X_proét`.
- `AlgebraicGeometry.ProEtale.FieldSheaf.unit`: the constant sheaf as a module over
  itself.
- `AlgebraicGeometry.ProEtale.fieldLowerStar`, `AlgebraicGeometry.ProEtale.fieldUpperStar`: `g_*`
  and `g^*`, with notations `(g)_*ᶠ[Λ]` and `(g)^*ᶠ[Λ]`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

/-- The sheaves of modules over the constant sheaf `Λ_X` on the small pro-étale site
of `X` (Bhatt–Scholze, §6.8): module objects over the monoid `Λ_X` in the monoidal category of
sheaves of `Λ`-modules. -/
abbrev FieldSheaf (X : Scheme.{u}) : Type (u + 2) :=
  Mod (Sheaf (Scheme.ProEt.topology X) (FieldCoefficients.{u} Λ)) (fieldConstantSheaf Λ X)

variable {Λ}

namespace FieldSheaf

variable (Λ) in
/-- The constant sheaf `Λ_X`, as a module over itself. -/
noncomputable abbrev unit (X : Scheme.{u}) : FieldSheaf Λ X :=
  Mod.regular (fieldConstantSheaf Λ X)

/-- The underlying sheaf of `Λ`-modules of a sheaf of `Λ_X`-modules. -/
noncomputable abbrev forget (X : Scheme.{u}) :
    FieldSheaf Λ X ⥤ Sheaf (Scheme.ProEt.topology X) (FieldCoefficients.{u} Λ) :=
  Mod.forget _

noncomputable instance (X : Scheme.{u}) : Abelian (FieldSheaf Λ X) :=
  Mod.instAbelian _

instance (X : Scheme.{u}) : IsGrothendieckAbelian.{u + 1} (FieldSheaf Λ X) :=
  Mod.isGrothendieckAbelian _

end FieldSheaf

section Functors

open scoped Obj

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

noncomputable instance : IsIso (((upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).homEquiv
    _ _).symm (fieldConstantSheafToLowerStar Λ g)) :=
  inferInstanceAs (IsIso (upperStarFieldConstantSheafHom Λ g))

instance : IsMonHom ((g)^*[FieldCoefficients.{u} Λ].map (fieldConstantSheafToLowerStar Λ g)) :=
  inferInstance

instance : IsMonHom (show (g)^*[FieldCoefficients.{u} Λ].obj ((g)_*[FieldCoefficients.{u} Λ].obj
      (fieldConstantSheaf Λ Z)) ⟶ fieldConstantSheaf Λ Z from
    (upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).counit.app
      (fieldConstantSheaf Λ Z)) := by
  have h := NatTrans.isMonHom_app (upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).counit
    (fieldConstantSheaf Λ Z)
  constructor
  · dsimp only
    simpa only [Functor.obj.η_def, Functor.LaxMonoidal.comp_ε, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_ε, Functor.id_map,
      Category.id_comp] using h.one_hom
  · dsimp only
    simpa only [Functor.obj.μ_def, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_μ, Functor.id_map,
      Category.id_comp] using h.mul_hom

instance : IsMonHom (((upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).homEquiv
    _ _).symm (fieldConstantSheafToLowerStar Λ g)) := by
  rw [Adjunction.homEquiv_counit]
  exact CategoryTheory.instIsMonHomComp _ (show (g)^*[FieldCoefficients.{u} Λ].obj
      ((g)_*[FieldCoefficients.{u} Λ].obj (fieldConstantSheaf Λ Z)) ⟶ fieldConstantSheaf Λ Z from
    (upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).counit.app
      (fieldConstantSheaf Λ Z))

variable (Λ) in
/-- The pushforward `g_*` of sheaves of modules over the constant sheaves `Λ_X`: the
pushforward of the underlying sheaf, a module over `Λ_Y` along `Λ_Y ⟶ g_* Λ_Z`. -/
noncomputable def fieldLowerStar : FieldSheaf Λ Z ⥤ FieldSheaf Λ Y :=
  (upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).modRight
    (fieldConstantSheafToLowerStar Λ g)

variable (Λ) in
/-- The pullback `g^*` of sheaves of modules over the constant sheaves `Λ_X`: the pullback of
the underlying sheaf, a module over `Λ_Z` along `g^* Λ_Y ≅ Λ_Z`. -/
noncomputable def fieldUpperStar : FieldSheaf Λ Y ⥤ FieldSheaf Λ Z :=
  (upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).modLeft
    (fieldConstantSheafToLowerStar Λ g)

@[inherit_doc fieldLowerStar]
scoped notation "(" g ")_*ᶠ[" Λ "]" => fieldLowerStar Λ g

@[inherit_doc fieldUpperStar]
scoped notation "(" g ")^*ᶠ[" Λ "]" => fieldUpperStar Λ g

variable (Λ) in
/-- The adjunction `g^* ⊣ g_*` on sheaves of modules over the constant sheaves `Λ_X`. -/
noncomputable def fieldUpperStarLowerStarAdjunction : (g)^*ᶠ[Λ] ⊣ (g)_*ᶠ[Λ] :=
  (upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).modAdjunction _

omit [IsUltrametricDist Λ] in
/-- The underlying sheaf of `g_* M` is the pushforward of the underlying sheaf of `M`. -/
lemma fieldLowerStar_obj_X (M : FieldSheaf Λ Z) :
    ((g)_*ᶠ[Λ].obj M).X = (g)_*[FieldCoefficients.{u} Λ].obj M.X :=
  rfl

/-- The underlying sheaf of `g^* M` is the pullback of the underlying sheaf of `M`. -/
lemma fieldUpperStar_obj_X (M : FieldSheaf Λ Y) :
    ((g)^*ᶠ[Λ].obj M).X = (g)^*[FieldCoefficients.{u} Λ].obj M.X :=
  rfl

omit [IsUltrametricDist Λ] in
lemma fieldLowerStar_map_hom {M N : FieldSheaf Λ Z} (f : M ⟶ N) :
    ((g)_*ᶠ[Λ].map f).hom = (g)_*[FieldCoefficients.{u} Λ].map f.hom :=
  rfl

lemma fieldUpperStar_map_hom {M N : FieldSheaf Λ Y} (f : M ⟶ N) :
    ((g)^*ᶠ[Λ].map f).hom = (g)^*[FieldCoefficients.{u} Λ].map f.hom :=
  rfl

instance : ((g)_*ᶠ[Λ]).Additive :=
  inferInstanceAs (Functor.mapMod _ _ ⋙ Mod.comap _).Additive

instance : ((g)^*ᶠ[Λ]).Additive :=
  inferInstanceAs (Functor.mapMod _ _ ⋙ Mod.comap _).Additive

instance : PreservesFiniteLimits (g)_*ᶠ[Λ] :=
  have : PreservesFiniteLimits ((g)_*ᶠ[Λ] ⋙ FieldSheaf.forget Y) :=
    inferInstanceAs (PreservesFiniteLimits (FieldSheaf.forget Z ⋙ (g)_*[FieldCoefficients.{u} Λ]))
  preservesFiniteLimits_of_reflects_of_preserves _ (FieldSheaf.forget Y)

instance : PreservesFiniteLimits (g)^*ᶠ[Λ] :=
  have : PreservesFiniteLimits ((g)^*ᶠ[Λ] ⋙ FieldSheaf.forget Z) :=
    inferInstanceAs (PreservesFiniteLimits (FieldSheaf.forget Y ⋙ (g)^*[FieldCoefficients.{u} Λ]))
  preservesFiniteLimits_of_reflects_of_preserves _ (FieldSheaf.forget Z)

instance : PreservesFiniteColimits (g)^*ᶠ[Λ] :=
  have : PreservesFiniteColimits ((g)^*ᶠ[Λ] ⋙ FieldSheaf.forget Z) :=
    inferInstanceAs
      (PreservesFiniteColimits (FieldSheaf.forget Y ⋙ (g)^*[FieldCoefficients.{u} Λ]))
  preservesFiniteColimits_of_reflects_of_preserves _ (FieldSheaf.forget Z)

end Functors

section Compat

variable (Λ)

omit [IsUltrametricDist Λ] in
/-- Pulling back functions along a composite is the composite of the pullbacks, up to the
composition isomorphism of pushforwards. -/
lemma fieldConstantSheafToLowerStar_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    fieldConstantSheafToLowerStar Λ h₂ ≫
        (h₂)_*[FieldCoefficients.{u} Λ].map (fieldConstantSheafToLowerStar Λ h₁) ≫
          (lowerStarComp (FieldCoefficients.{u} Λ) h₁ h₂).hom.app (fieldConstantSheaf Λ T) =
      fieldConstantSheafToLowerStar Λ (h₁ ≫ h₂) := by
  ext V : 3
  ext x
  refine fieldConstantSheaf_ext (Λ := Λ) fun y ↦ ?_
  have key : ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h₁ h₂).hom.app
      V.unop).left ≫ pullback.fst _ h₁ ≫ pullback.fst V.unop.hom h₂ =
        pullback.fst V.unop.hom (h₁ ≫ h₂) := by
    simp only [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, NatIso.ofComponents_hom_app, MorphismProperty.Over.isoMk_hom_left]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.congrHom_hom]
    erw [pullback.map_id, Category.id_comp]
    exact pullbackLeftPullbackSndIso_inv_fst _ _ _
  exact congrArg (fun φ ↦ x.down.1 (φ.base y)) key

omit [IsUltrametricDist Λ] in
/-- Pulling back functions along the identity is the identity, up to the identification
`(𝟙 X)_* ≅ 𝟭`. -/
lemma fieldConstantSheafToLowerStar_id (X : Scheme.{u}) :
    fieldConstantSheafToLowerStar Λ (𝟙 X) ≫
        (lowerStarId (FieldCoefficients.{u} Λ) X).hom.app (fieldConstantSheaf Λ X) = 𝟙 _ := by
  ext V : 3
  ext x
  refine fieldConstantSheaf_ext (Λ := Λ) fun y ↦ ?_
  have key : ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).left ≫
      pullback.fst V.unop.hom (𝟙 X) = 𝟙 _ := by
    simp [MorphismProperty.Over.pullbackId]
  exact congrArg (fun φ ↦ x.down.1 (φ.base y)) key

end Compat

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

section Isos

instance {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    NatTrans.IsMonoidal (lowerStarComp (FieldCoefficients.{u} Λ) h₁ h₂).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h₁ h₂).symm)
    (FieldCoefficients.{u} Λ) (Scheme.ProEt.topology R) (Scheme.ProEt.topology S)
    (Scheme.ProEt.topology T)).hom)

instance (X : Scheme.{u}) : NatTrans.IsMonoidal (lowerStarId (FieldCoefficients.{u} Λ) X).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) (FieldCoefficients.{u} Λ)
    (Scheme.ProEt.topology X)).hom)

variable (Λ) in
/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of sheaves of modules over the
constant sheaves `Λ_X`: that of the underlying sheaves, which is linear. -/
noncomputable def fieldLowerStarComp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    (h₁)_*ᶠ[Λ] ⋙ (h₂)_*ᶠ[Λ] ≅ (h₁ ≫ h₂)_*ᶠ[Λ] :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk ((lowerStarComp (FieldCoefficients.{u} Λ) h₁ h₂).app M.X)
      (Functor.act_comp_app_of_isMonoidal (lowerStarComp (FieldCoefficients.{u} Λ) h₁ h₂).hom
        (fieldConstantSheafToLowerStar Λ h₁) (fieldConstantSheafToLowerStar Λ h₂)
        (fieldConstantSheafToLowerStar Λ (h₁ ≫ h₂)) (fieldConstantSheafToLowerStar_comp Λ h₁ h₂) M))
    fun f ↦ Mod.hom_ext _ _ ((lowerStarComp (FieldCoefficients.{u} Λ) h₁ h₂).hom.naturality f.hom)

variable (Λ) in
/-- The identity isomorphism `(𝟙 X)_* ≅ 𝟭` of sheaves of modules over the constant
sheaf. -/
noncomputable def fieldLowerStarId (X : Scheme.{u}) : (𝟙 X)_*ᶠ[Λ] ≅ 𝟭 (FieldSheaf Λ X) :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk (M := (𝟙 X)_*ᶠ[Λ].obj M) (N := (Mod.comap (D := Sheaf _ _)
        (𝟙 (fieldConstantSheaf Λ X))).obj M) ((lowerStarId (FieldCoefficients.{u} Λ) X).app M.X)
      (Functor.act_comp_app_of_isMonoidal_id (lowerStarId (FieldCoefficients.{u} Λ) X).hom
        (fieldConstantSheafToLowerStar Λ (𝟙 X)) (𝟙 _)
        (fieldConstantSheafToLowerStar_id Λ X) M))
    (fun f ↦ Mod.hom_ext _ _ ((lowerStarId (FieldCoefficients.{u} Λ) X).hom.naturality f.hom)) ≪≫
  Mod.comapId _

variable (Λ) in
/-- The pushforwards of sheaves of modules along equal morphisms are isomorphic. -/
noncomputable def fieldLowerStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)_*ᶠ[Λ] ≅ (g')_*ᶠ[Λ] :=
  NatIso.ofComponents (fun M ↦ Mod.isoMk (M := (g)_*ᶠ[Λ].obj M) (N := (g')_*ᶠ[Λ].obj M)
      ((lowerStarCongr (FieldCoefficients.{u} Λ) h).app M.X) (by
        subst h
        simp only [lowerStarCongr_rfl, Iso.app_hom, Iso.refl_hom, NatTrans.id_app]
        erw [Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]))
    fun f ↦ Mod.hom_ext _ _ ((lowerStarCongr (FieldCoefficients.{u} Λ) h).hom.naturality f.hom)

omit [IsUltrametricDist Λ] in
lemma fieldLowerStarCongr_hom_app_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (M : FieldSheaf Λ Z) :
    ((fieldLowerStarCongr Λ h).hom.app M).hom =
      (lowerStarCongr (FieldCoefficients.{u} Λ) h).hom.app M.X :=
  rfl

omit [IsUltrametricDist Λ] in
lemma fieldLowerStarComp_hom_app_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : FieldSheaf Λ T) :
    ((fieldLowerStarComp Λ h₁ h₂).hom.app M).hom =
      (lowerStarComp (FieldCoefficients.{u} Λ) h₁ h₂).hom.app M.X :=
  rfl

omit [IsUltrametricDist Λ] in
lemma fieldLowerStarComp_inv_app_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : FieldSheaf Λ T) :
    ((fieldLowerStarComp Λ h₁ h₂).inv.app M).hom =
      (lowerStarComp (FieldCoefficients.{u} Λ) h₁ h₂).inv.app M.X :=
  rfl

variable (Λ) in
/-- The pullbacks of sheaves of modules along equal morphisms are isomorphic. -/
noncomputable def fieldUpperStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)^*ᶠ[Λ] ≅ (g')^*ᶠ[Λ] :=
  eqToIso (by rw [h])

variable (Λ) in
/-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭` of sheaves of modules over the constant
sheaf, by uniqueness of left adjoints. -/
noncomputable def fieldUpperStarId (X : Scheme.{u}) : (𝟙 X)^*ᶠ[Λ] ≅ 𝟭 (FieldSheaf Λ X) :=
  (conjugateIsoEquiv Adjunction.id (fieldUpperStarLowerStarAdjunction Λ (𝟙 X))).symm
    (fieldLowerStarId Λ X).symm

variable (Λ) in
/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of sheaves of modules over the
constant sheaves `Λ_X`, by uniqueness of left adjoints. -/
noncomputable def fieldUpperStarComp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    (h₁ ≫ h₂)^*ᶠ[Λ] ≅ (h₂)^*ᶠ[Λ] ⋙ (h₁)^*ᶠ[Λ] :=
  ((conjugateIsoEquiv (fieldUpperStarLowerStarAdjunction Λ (h₁ ≫ h₂))
      ((fieldUpperStarLowerStarAdjunction Λ h₂).comp (fieldUpperStarLowerStarAdjunction Λ h₁))).symm
    (fieldLowerStarComp Λ h₁ h₂).symm).symm

variable (Λ) in
/-- The pullbacks along the two sides of a commutative square agree. -/
noncomputable def fieldUpperStarCompIso {Y Z₁ Z₂ T : Scheme.{u}} {a : Y ⟶ Z₁} {b : Z₁ ⟶ T}
    {c : Y ⟶ Z₂} {d : Z₂ ⟶ T} (h : a ≫ b = c ≫ d) :
    (b)^*ᶠ[Λ] ⋙ (a)^*ᶠ[Λ] ≅ (d)^*ᶠ[Λ] ⋙ (c)^*ᶠ[Λ] :=
  (fieldUpperStarComp Λ a b).symm ≪≫ fieldUpperStarCongr Λ h ≪≫ fieldUpperStarComp Λ c d

variable (Λ) in
/-- The congruence isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_fieldUpperStarCongr_inv {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g') :
    conjugateEquiv (fieldUpperStarLowerStarAdjunction Λ g) (fieldUpperStarLowerStarAdjunction Λ g')
      (fieldUpperStarCongr Λ h).inv = (fieldLowerStarCongr Λ h).hom := by
  subst h
  refine NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_)
  simp [fieldUpperStarCongr, fieldLowerStarCongr_hom_app_hom]
  rfl

variable (Λ) in
/-- The inverse of the composition isomorphism of pullbacks is conjugate to that of
pushforwards. -/
lemma conjugateEquiv_fieldUpperStarComp_inv {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateEquiv (fieldUpperStarLowerStarAdjunction Λ (h₁ ≫ h₂))
      ((fieldUpperStarLowerStarAdjunction Λ h₂).comp (fieldUpperStarLowerStarAdjunction Λ h₁))
      (fieldUpperStarComp Λ h₁ h₂).inv = (fieldLowerStarComp Λ h₁ h₂).inv :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (fieldLowerStarComp Λ h₁ h₂).symm)

variable (Λ) in
/-- The composition isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_fieldUpperStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateEquiv ((fieldUpperStarLowerStarAdjunction Λ h₂).comp
        (fieldUpperStarLowerStarAdjunction Λ h₁))
      (fieldUpperStarLowerStarAdjunction Λ (h₁ ≫ h₂)) (fieldUpperStarComp Λ h₁ h₂).hom =
        (fieldLowerStarComp Λ h₁ h₂).hom := by
  have := conjugateEquiv_comm (fieldUpperStarLowerStarAdjunction Λ (h₁ ≫ h₂))
    ((fieldUpperStarLowerStarAdjunction Λ h₂).comp (fieldUpperStarLowerStarAdjunction Λ h₁))
    (α := (fieldUpperStarComp Λ h₁ h₂).inv) (β := (fieldUpperStarComp Λ h₁ h₂).hom) (by simp)
  rw [conjugateEquiv_fieldUpperStarComp_inv] at this
  rw [← cancel_epi (fieldLowerStarComp Λ h₁ h₂).inv, this, Iso.inv_hom_id]

variable (Λ) in
/-- **The pullback of the constant sheaf is the constant sheaf**, as sheaves
of modules over the constant sheaf: `g^* Λ_Y ≅ Λ_Z`
(`AlgebraicGeometry.ProEtale.upperStarFieldConstantSheafIso`, a ring isomorphism). -/
noncomputable def fieldUpperStarUnitIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (g)^*ᶠ[Λ].obj (FieldSheaf.unit Λ Y) ≅ FieldSheaf.unit Λ Z :=
  Mod.regularIsoOfIsIso _

variable (Λ) in
/-- **The pushforward of the constant sheaf along an isomorphism** `e : X ≅ Y` is the
constant sheaf, as sheaves of modules: the inverse of the ring isomorphism
`Λ_Y ⟶ e_* Λ_X`, whose underlying morphism is
`AlgebraicGeometry.ProEtale.fieldConstantSheafLowerStarIso`. -/
noncomputable def fieldLowerStarUnitIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (e.hom)_*ᶠ[Λ].obj (FieldSheaf.unit Λ X) ≅ FieldSheaf.unit Λ Y :=
  Mod.isoMk (M := (e.hom)_*ᶠ[Λ].obj (FieldSheaf.unit Λ X)) (N := FieldSheaf.unit Λ Y)
    (fieldConstantSheafLowerStarIso Λ e) (by
      have : IsMonHom (fieldConstantSheafLowerStarIso Λ e).inv :=
        inferInstanceAs (IsMonHom (fieldConstantSheafToLowerStar Λ e.hom))
      have : IsMonHom (fieldConstantSheafLowerStarIso Λ e).hom := by
        have : IsMonHom (inv (fieldConstantSheafLowerStarIso Λ e).inv) := inferInstance
        rwa [IsIso.Iso.inv_inv] at this
      have h := IsMonHom.mul_hom (f := (fieldConstantSheafLowerStarIso Λ e).hom)
      change ((fieldConstantSheafLowerStarIso Λ e).inv ▷ _ ≫ μ) ≫ _ = _
      rw [Category.assoc, h, tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc,
        Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
      rfl)

omit [IsUltrametricDist Λ] in
lemma fieldLowerStarUnitIso_hom_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    (fieldLowerStarUnitIso Λ e).hom.hom = (fieldConstantSheafLowerStarIso Λ e).hom :=
  rfl

end Isos

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.FieldSheaf

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ] {X : Scheme.{u}}

/-- Multiplication by a scalar `c ∈ Λ`, an endomorphism of a sheaf of `Λ_X`-modules. -/
noncomputable def smul (c : ULift.{u + 1} Λ) (M : FieldSheaf Λ X) : M ⟶ M :=
  Mod.homMk (c • 𝟙 M.X) (by
    rw [Linear.comp_smul, Category.comp_id, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])

omit [IsUltrametricDist Λ] in
@[simp]
lemma smul_hom (c : ULift.{u + 1} Λ) (M : FieldSheaf Λ X) :
    (smul c M).hom = c • 𝟙 M.X :=
  rfl

omit [IsUltrametricDist Λ] in
lemma smul_comp (c : ULift.{u + 1} Λ) {M N : FieldSheaf Λ X} (f : M ⟶ N) :
    smul c M ≫ f = f ≫ smul c N :=
  Mod.hom_ext _ _ (by simp)

omit [IsUltrametricDist Λ] in
lemma smul_smul (c d : ULift.{u + 1} Λ) (M : FieldSheaf Λ X) :
    smul c M ≫ smul d M = smul (d * c) M :=
  Mod.hom_ext _ _ (by simp [_root_.smul_smul])

omit [IsUltrametricDist Λ] in
lemma smul_one (M : FieldSheaf Λ X) : smul 1 M = 𝟙 M :=
  Mod.hom_ext _ _ (by simp)

omit [IsUltrametricDist Λ] in
/-- The pushforward commutes with multiplication by a scalar. -/
lemma fieldLowerStar_map_smul {Z : Scheme.{u}} (g : X ⟶ Z) (c : ULift.{u + 1} Λ)
    (M : FieldSheaf Λ X) : (g)_*ᶠ[Λ].map (smul c M) = smul c ((g)_*ᶠ[Λ].obj M) :=
  Mod.hom_ext _ _ (by ext : 3; rfl)

end AlgebraicGeometry.ProEtale.FieldSheaf
