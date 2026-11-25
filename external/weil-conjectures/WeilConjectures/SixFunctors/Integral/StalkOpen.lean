/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Integral.StalkPatch

/-!
# Vanishing of restricted germs is an open condition on the geometric fibre

Consider a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
with `f` integral, a geometric point `y'` of `Y'` with algebraically closed residue field, and
an affine pointed étale neighbourhood `(U₀, u₀)` of `y' ≫ g`. For a germ `d` of `f'_* G` at
`y'` whose restriction to a geometric point `t₀` of `X'` over `y'` vanishes, the restriction of
`d` to every geometric point `t` of `X'` over `y'` whose image in `X` agrees at `(u₀, t ≫ g')`
with `(u₀, t₀ ≫ g')` on finitely many functions on `U₀ ×_Y X` vanishes as well
(`AlgebraicGeometry.Etale.exists_finset_stalkRestrict_eq_zero`).

The germ is a section `σ` of `G` over `V ×_{Y'} X'` for an affine pointed étale neighbourhood
`(V, v)` of `y'` mapping to `U₀`, the vanishing set of `σ` contains a basic open `D(h)` around
`(v, t₀)`, and `V ×_{Y'} X' = V ×_{U₀} (U₀ ×_Y X)` so the value of `h` at `(v, t)` only
depends on the values of finitely many functions on `U₀ ×_Y X` at `(u₀, t ≫ g')`
(`AlgebraicGeometry.Scheme.Hom.exists_finset_appTopPoint_eq_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme Scheme.Hom

variable (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} [IsIntegralHom f]

/-- **Vanishing of restricted germs is an open condition on the geometric fibre.** For a
cartesian square with `f` integral, an affine pointed étale neighbourhood `(U₀, u₀)` of
`y' ≫ g` and a germ `d` of `f'_* G` at `y'` whose restriction to the geometric point `t₀` of
`X'` over `y'` vanishes, there is a finite set `S` of functions on `U₀ ×_Y X` such that the
restriction of `d` to every `t` whose point `(u₀, t ≫ g')` agrees with `(u₀, t₀ ≫ g')` on
`S` vanishes. -/
theorem Etale.exists_finset_stalkRestrict_eq_zero (sq : IsPullback g' f' f g)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y')
    (c₀ : Nbhd (y' ≫ g)) [IsAffine c₀.1.left]
    (G : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (d : ToType ((pointSmallEtale y').sheafFiber.obj ((f')_*[ModuleCat.{u + 1} Λ].obj G)))
    (t₀ : f'.GeometricFiber y')
    (hd : Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f' y' t₀ G d = 0) :
    ∃ S : Finset Γ(pullback c₀.1.hom f, ⊤), ∀ t : f'.GeometricFiber y',
      (∀ b ∈ S, (basePt f c₀ (GeometricFiber.baseChangeEquiv sq y' t)).appTopPoint b =
        (basePt f c₀ (GeometricFiber.baseChangeEquiv sq y' t₀)).appTopPoint b) →
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f' y' t G d = 0 := by
  have : IsIntegralHom f' := MorphismProperty.of_isPullback sq inferInstance
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨V, v, σ, rfl⟩ := (pointSmallEtale y').toPresheafFiber_jointly_surjective
    (P := ((f')_*[ModuleCat.{u + 1} Λ].obj G).obj) d
  -- an affine pointed étale neighbourhood of `y'` refining `(V, v)` and mapping to `U₀`
  let c₁ : Nbhd y' := Functor.elementsMk _ V v
  let c₀' : Nbhd y' := (Etale.baseChangeNbhd g (y' ≫ g) ⟨y', rfl⟩).obj c₀
  obtain ⟨c, h₂, hc⟩ := Nbhd.exists_hom_isAffine (IsCofiltered.min c₁ c₀')
  let k₁ : c ⟶ c₁ := h₂ ≫ IsCofiltered.minToLeft c₁ c₀'
  let k₀ : c ⟶ c₀' := h₂ ≫ IsCofiltered.minToRight c₁ c₀'
  -- the section over `c`, and its germs
  let σ' : ToType (G.obj.obj (op (f'.Etale.obj c.1))) :=
    ((f')_*[ModuleCat.{u + 1} Λ].obj G).obj.map k₁.val.op σ
  have hgerm : (pointSmallEtale y').toPresheafFiber c₁.1 c₁.2
      ((f')_*[ModuleCat.{u + 1} Λ].obj G).obj σ =
      (pointSmallEtale y').toPresheafFiber c.1 c.2 ((f')_*[ModuleCat.{u + 1} Λ].obj G).obj
        σ' := by
    have h := (pointSmallEtale y').toPresheafFiber_w_apply k₁.val c.2
      ((f')_*[ModuleCat.{u + 1} Λ].obj G).obj σ
    rw [Functor.Elements.Hom.val, k₁.map_val] at h
    exact h.symm
  have hres (t : f'.GeometricFiber y') :
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f' y' t G
        ((pointSmallEtale y').toPresheafFiber c₁.1 c₁.2
          ((f')_*[ModuleCat.{u + 1} Λ].obj G).obj σ) = 0 ↔
      basePt f' c t default ∈ Etale.vanishingSet Λ G σ' := by
    rw [hgerm]
    have h : Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f' y' t G
        ((pointSmallEtale y').toPresheafFiber c.1 c.2 ((f')_*[ModuleCat.{u + 1} Λ].obj G).obj
          σ') =
        (pointSmallEtale t.1).toPresheafFiber _ ((Etale.baseChangeNbhd f' y' t).obj c).2 G.obj
          σ' :=
      ConcreteCategory.congr_hom
        (Etale.toPresheafFiber_stalkRestrict (ModuleCat.{u + 1} Λ) f' y' t G c) σ'
    rw [h]
    exact Etale.toPresheafFiber_eq_zero_iff_mem_vanishingSet Λ G σ' t.1 _
  -- a basic open around `(v, t₀)` on which `σ'` vanishes
  have : IsAffine ((𝟭 Scheme).obj c.1.left) := hc
  have : IsAffine (pullback c.1.hom f') := isAffine_of_isAffineHom (pullback.fst c.1.hom f')
  have : IsAffine ((𝟭 Scheme).obj c₀.1.left) := ‹IsAffine c₀.1.left›
  have : IsAffine (pullback c₀.1.hom f) := isAffine_of_isAffineHom (pullback.fst c₀.1.hom f)
  obtain ⟨_, ⟨h, rfl⟩, hx, hle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen (pullback c.1.hom f'))
      (U := ⟨_, Etale.isOpen_vanishingSet Λ G σ'⟩) ((hres t₀).1 hd)
  -- the square `V ×_{Y'} X' = V ×_{U₀} (U₀ ×_Y X)`
  let κ : c.1.left ⟶ c₀.1.left := k₀.val.left ≫ pullback.fst c₀.1.hom g
  have hκ : κ ≫ c₀.1.hom = c.1.hom ≫ g := by
    simp only [κ, Category.assoc, pullback.condition]
    rw [← Category.assoc]
    congr 1
    exact MorphismProperty.Over.w k₀.val
  let ψ : pullback c.1.hom f' ⟶ pullback c₀.1.hom f :=
    pullback.lift (pullback.fst c.1.hom f' ≫ κ) (pullback.snd c.1.hom f' ≫ g') (by
      rw [Category.assoc, hκ, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, sq.w])
  have hs : IsPullback (ψ ≫ pullback.snd c₀.1.hom f) (pullback.fst c.1.hom f') f
      (κ ≫ c₀.1.hom) := by
    rw [pullback.lift_snd, hκ]
    exact (IsPullback.of_hasPullback c.1.hom f').flip.paste_horiz sq
  have hP : IsPullback (pullback.fst c.1.hom f') ψ κ (pullback.fst c₀.1.hom f) :=
    (IsPullback.of_right hs (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback c₀.1.hom f).flip).flip
  obtain ⟨S₁, S₂, hS⟩ :=
    Scheme.Hom.exists_finset_appTopPoint_eq_of_isPullback hP (Ω := Ω) h
  -- the points `(v, t)` map to the points `(u₀, t ≫ g')`
  have hpt (t : f'.GeometricFiber y') :
      basePt f' c t ≫ ψ = basePt f c₀ (GeometricFiber.baseChangeEquiv sq y' t) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, basePt_fst_assoc, basePt_fst]
      simp only [κ, ← Category.assoc]
      rw [show c.2.left ≫ k₀.val.left = c₀'.2.left from
        congrArg CategoryTheory.Over.Hom.left k₀.2]
      exact basePt_fst g c₀ ⟨y', rfl⟩
    · rw [Category.assoc, pullback.lift_snd, basePt_snd_assoc, basePt_snd,
        GeometricFiber.baseChangeEquiv_apply_coe]
  refine ⟨S₂, fun t ht ↦ (hres t).2 (hle ?_)⟩
  rw [Scheme.Hom.apply_default_mem_basicOpen_iff] at hx ⊢
  rwa [hS (basePt f' c t) (basePt f' c t₀) (fun a _ ↦ by rw [basePt_fst, basePt_fst])
    (fun b hb ↦ by rw [hpt, hpt]; exact ht b hb)]

end AlgebraicGeometry
