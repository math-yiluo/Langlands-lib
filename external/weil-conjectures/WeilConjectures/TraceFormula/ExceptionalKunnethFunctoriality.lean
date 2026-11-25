/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.LowerShriekCoherence

/-!

# Functoriality of the exceptional Künneth map in the second factor

Let `X, Y, Z` be separated `k`-schemes of finite type and `g : Z ⟶ Y`. Write
`G = 𝟙_X × g : X ⨯ Z ⟶ X ⨯ Y`, `p : X ⨯ Y ⟶ X`, `q : X ⨯ Y ⟶ Y`, `p_Z : X ⨯ Z ⟶ X`,
`q_Z : X ⨯ Z ⟶ Z` for the projections, so that `G ≫ p = p_Z`, `G ≫ q = q_Z ≫ g`, and the square
`(q_Z, G, g, q)` is cartesian (`ProEtale.CondensedRing.isPullback_prodMap_id`).

The *trace* of `G` on external products with the dualizing complexes
(`ProEtale.CondensedRing.exceptionalKunnethProdMapTrace`) is the composite
```
RG_! (M ⊠ ω_Z) ≅ RG_! (Lq_Z^* ω_Z ⊗ LG^* Lp^* M) ≅ RG_! Lq_Z^* ω_Z ⊗ Lp^* M
  ≅ Lq^* Rg_! ω_Z ⊗ Lp^* M ≅ Lq^* Rg_! Rg^! ω_Y ⊗ Lp^* M --ε--> Lq^* ω_Y ⊗ Lp^* M ≅ M ⊠ ω_Y
```
of the symmetry, the inverse of the projection formula for `G`, the inverse of compact-support
base change in the cartesian square, the identification `ω_Z ≅ Rg^! ω_Y` and the counit of
`Rg_! ⊣ Rg^!`. The exceptional Künneth map `α` (`ProEtale.CondensedRing.exceptionalKunnethMap`)
is compatible with it: the adjoint of `α_Z` is the composite of `Rp_Z! ≅ Rp_! RG_!`, of `Rp_!` of
the trace and of the adjoint of `α_Y`
(`ProEtale.CondensedRing.exceptionalKunnethAdjoint_comp_prodMap`);
equivalently `α_Z` is the transpose along `RG_! ⊣ RG^!` of `trace ≫ α_Y`, followed by
`RG^! Rp^! ≅ Rp_Z^!` (`ProEtale.CondensedRing.exceptionalKunnethMap_comp_prodMap`).

The proof uses the compatibility of the projection formula with composition and of
compact-support base change with pasting (`WeilConjectures.TraceFormula.LowerShriekCoherence`,
`WeilConjectures.TraceFormula.BaseChangeCoherence`), and the description of the counit of a
composite adjunction through the conjugate composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`.
The diagram chase is carried out for abstract functors, and first for an arbitrary cartesian
square `q_W ≫ g = G ≫ q_V` over `X` (`exceptionalKunnethAdjoint_comp_of_isPullback`): stating it
for general objects keeps the terms compared by the kernel small.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekCompOfEq`,
  `ProEtale.CondensedRing.boundedConstructibleUpperStarCompOfEq`,
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekCompOfEq`: the composition isomorphisms
  for a factorisation `f₁ ≫ f₂ = f`.
- `ProEtale.CondensedRing.exceptionalKunnethTraceOfSquare`: the trace map of a cartesian square.
- `ProEtale.CondensedRing.exceptionalKunnethProdMapTrace`: the trace map
  `RG_! (M ⊠ ω_Z) ⟶ M ⊠ ω_Y`.

## Main statements

- `ProEtale.CondensedRing.exceptionalKunnethAdjoint_comp_of_isPullback`
- `ProEtale.CondensedRing.exceptionalKunnethAdjoint_comp_prodMap`
- `ProEtale.CondensedRing.exceptionalKunnethMap_comp_prodMap`

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Composition isomorphisms along a factorisation -/

section CompOfEq

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  {f₁ : X ⟶ Y} {f₂ : Y ⟶ S} {f : X ⟶ S}

/-- The composition isomorphism `Rf_! ≅ Rf₁_! ⋙ Rf₂_!` for a factorisation `f₁ ≫ f₂ = f`. -/
noncomputable def boundedConstructibleLowerShriekCompOfEq (h : f₁ ≫ f₂ = f) :
    boundedConstructibleLowerShriek ℓ f ≅
      boundedConstructibleLowerShriek ℓ f₁ ⋙
        boundedConstructibleLowerShriek ℓ f₂ :=
  eqToIso (by rw [h]) ≪≫ boundedConstructibleLowerShriekComp_padicAlgCl ℓ f₁ f₂

/-- The composition isomorphism `Lf^* ≅ Lf₂^* ⋙ Lf₁^*` for a factorisation `f₁ ≫ f₂ = f`. -/
noncomputable def boundedConstructibleUpperStarCompOfEq (h : f₁ ≫ f₂ = f) :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f₂ ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f₁ :=
  eqToIso (by rw [h]) ≪≫ boundedConstructibleUpperStarComp _ ℓ f₁ f₂

/-- The composition isomorphism `Rf^! ≅ Rf₂^! ⋙ Rf₁^!` for a factorisation `f₁ ≫ f₂ = f`. -/
noncomputable def boundedConstructibleUpperShriekCompOfEq (h : f₁ ≫ f₂ = f) :
    boundedConstructibleUpperShriek ℓ f ≅
      boundedConstructibleUpperShriek ℓ f₂ ⋙
        boundedConstructibleUpperShriek ℓ f₁ :=
  eqToIso (by rw [h]) ≪≫ boundedConstructibleUpperShriekComp_padicAlgCl ℓ f₁ f₂

/-- The composition isomorphism of the exceptional inverse images along a factorisation is the
conjugate of that of the lower shrieks. -/
lemma boundedConstructibleUpperShriekCompOfEq_eq (h : f₁ ≫ f₂ = f) :
    boundedConstructibleUpperShriekCompOfEq ℓ h =
      conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
        ((boundedConstructibleUpperShriekAdjunction ℓ f₁).comp
          (boundedConstructibleUpperShriekAdjunction ℓ f₂))
        (boundedConstructibleLowerShriekCompOfEq ℓ h).symm := by
  subst h
  ext : 1
  simp [boundedConstructibleUpperShriekCompOfEq, boundedConstructibleLowerShriekCompOfEq,
    boundedConstructibleUpperShriekComp_padicAlgCl]

/-- The projection formula along a factorisation `f₁ ≫ f₂ = f`
(`boundedConstructibleExceptionalProjectionMorphism_comp`). -/
lemma boundedConstructibleExceptionalProjectionMorphism_comp_of_eq (h : f₁ ≫ f₂ = f)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ f K B ≫
        (boundedConstructibleLowerShriekCompOfEq ℓ h).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) ≫
        (boundedConstructibleLowerShriek ℓ f₂).map ((boundedConstructibleLowerShriek ℓ f₁).map
          (K ◁ (boundedConstructibleUpperStarCompOfEq ℓ h).hom.app B)) =
      (boundedConstructibleLowerShriekCompOfEq ℓ h).hom.app K ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ f₂
          ((boundedConstructibleLowerShriek ℓ f₁).obj K) B ≫
        (boundedConstructibleLowerShriek ℓ f₂).map
          (boundedConstructibleExceptionalProjectionMorphism ℓ f₁ K
            ((boundedConstructibleUpperStar _ ℓ f₂).obj B)) := by
  subst h
  simpa [boundedConstructibleLowerShriekCompOfEq, boundedConstructibleUpperStarCompOfEq] using
    boundedConstructibleExceptionalProjectionMorphism_comp ℓ f₁ f₂ K B

/-- The counit of `Rf_! ⊣ Rf^!` along a factorisation `f₁ ≫ f₂ = f`: it is the counit of the
composite adjunction `Rf₁_! ⋙ Rf₂_! ⊣ Rf₂^! ⋙ Rf₁^!`, through the composition isomorphisms. -/
lemma boundedConstructibleUpperShriekAdjunction_counit_app_of_eq (h : f₁ ≫ f₂ = f)
    (B : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (d : (boundedConstructibleUpperShriek ℓ f₁).obj
        ((boundedConstructibleUpperShriek ℓ f₂).obj B) ≅
      (boundedConstructibleUpperShriek ℓ f).obj B)
    (hB : (boundedConstructibleUpperShriek ℓ (f₁ ≫ f₂)).obj B =
      (boundedConstructibleUpperShriek ℓ f).obj B)
    (hd : d = ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f₁ f₂).app B).symm ≪≫
      eqToIso hB) :
    (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app B =
      (boundedConstructibleLowerShriekCompOfEq ℓ h).hom.app _ ≫
        (boundedConstructibleLowerShriek ℓ f₂).map
          ((boundedConstructibleLowerShriek ℓ f₁).map d.inv ≫
            (boundedConstructibleUpperShriekAdjunction ℓ f₁).counit.app
              ((boundedConstructibleUpperShriek ℓ f₂).obj B)) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ f₂).counit.app B := by
  subst h hd
  simp [boundedConstructibleLowerShriekCompOfEq, boundedConstructibleUpperShriekComp_padicAlgCl]

end CompOfEq
section PasteVert

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Over (Spec (.of k))}
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
  [LocallyOfFiniteType Y₃.hom] [QuasiCompact Y₃.hom] [IsSeparated Y₃.hom]

/-- Vertical pasting of `Ex_!` (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert`)
for an outer cartesian square whose vertical maps are given factorisations `v₁ ≫ w₁ = f'` and
`v₂ ≫ w₂ = f`. -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert_of_eq
    {h : X₁ ⟶ X₂} {v₁ : X₁ ⟶ Y₁} {v₂ : X₂ ⟶ Y₂} {k : Y₁ ⟶ Y₂} {w₁ : Y₁ ⟶ X₃} {w₂ : Y₂ ⟶ Y₃}
    {l : X₃ ⟶ Y₃} {f' : X₁ ⟶ X₃} {f : X₂ ⟶ Y₃} (sq : IsPullback h f' f l)
    (sq₁ : IsPullback h v₁ v₂ k) (sq₂ : IsPullback k w₁ w₂ l) (hf' : v₁ ≫ w₁ = f')
    (hf : v₂ ≫ w₂ = f) (M : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app M ≫
        (boundedConstructibleLowerShriekCompOfEq ℓ hf').hom.app
          ((boundedConstructibleUpperStar _ ℓ h).obj M) =
      (boundedConstructibleUpperStar _ ℓ l).map
          ((boundedConstructibleLowerShriekCompOfEq ℓ hf).hom.app M) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂).app
          ((boundedConstructibleLowerShriek ℓ v₂).obj M) ≫
        (boundedConstructibleLowerShriek ℓ w₁).map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app M) := by
  subst hf' hf
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert ℓ sq₁ sq₂ M]
  simp [boundedConstructibleLowerShriekCompOfEq]

end PasteVert

/-! ### The abstract diagram chases -/

/-- The diagram chase behind `exceptionalKunnethAdjoint_comp_prodMap`, for abstract functors:
`P_Z ≅ G ⋙ P` plays `Rp_Z! ≅ RG_! ⋙ Rp_!`, `pfZ`, `pfp` and `pfG` the projection morphisms of
`p_Z`, `p` and `G`, `bz` and `bcY` the inverse base changes of the product squares, `bs` the base
change of the square of `G`, `εZ`, `εY` the counits at the unit and `ψ : Rg_! ω_Z ⟶ ω_Y`. -/
private lemma exceptionalKunnethAdjoint_comp_prodMap_aux {𝒳 𝒱 𝒲 𝒮 𝒴 : Type*} [Category 𝒳]
    [Category 𝒱] [Category 𝒲] [Category 𝒮] [Category 𝒴] [MonoidalCategory 𝒳]
    [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [BraidedCategory 𝒱] [BraidedCategory 𝒲]
    (PZ : 𝒱 ⥤ 𝒳) (G : 𝒱 ⥤ 𝒲) (P : 𝒲 ⥤ 𝒳) (c : PZ ≅ G ⋙ P) (Fx : 𝒮 ⥤ 𝒳) (Ay : 𝒴 ⥤ 𝒮)
    (Q : 𝒴 ⥤ 𝒲) (bcY : Q ⋙ P ≅ Ay ⋙ Fx) (M : 𝒳) {A B B' : 𝒱} (e : B ⟶ B') (pM : 𝒲)
    (pfZ : PZ.obj A ⊗ M ⟶ PZ.obj (A ⊗ B)) [IsIso pfZ]
    (pfp : ∀ W : 𝒲, P.obj W ⊗ M ⟶ P.obj (W ⊗ pM)) [∀ W, IsIso (pfp W)]
    (hpfp : ∀ {W W' : 𝒲} (f : W ⟶ W'), P.map f ▷ M ≫ pfp W' = pfp W ≫ P.map (f ▷ pM))
    (pfG : G.obj A ⊗ pM ⟶ G.obj (A ⊗ B')) [IsIso pfG]
    (h₁ : pfZ ≫ c.hom.app (A ⊗ B) ≫ P.map (G.map (A ◁ e)) =
      c.hom.app A ▷ M ≫ pfp (G.obj A) ≫ P.map pfG)
    {Z₀ : 𝒮} (bz : PZ.obj A ≅ Fx.obj Z₀) {gω ωY : 𝒴} (t : Z₀ ⟶ Ay.obj gω)
    (bs : Q.obj gω ⟶ G.obj A) [IsIso bs]
    (h₂ : bz.inv ≫ c.hom.app A = Fx.map t ≫ bcY.inv.app gω ≫ P.map bs)
    {I : 𝒮} (εZ : Z₀ ⟶ I) (εY : Ay.obj ωY ⟶ I) (ψ : gω ⟶ ωY)
    (h₃ : εZ = t ≫ Ay.map ψ ≫ εY) (u : Fx.obj I ⟶ 𝟙_ 𝒳) :
    PZ.map (β_ B A).hom ≫ inv pfZ ≫ bz.hom ▷ M ≫ Fx.map εZ ▷ M ≫ u ▷ M ≫ (λ_ M).hom =
      c.hom.app (B ⊗ A) ≫ P.map (G.map (β_ B A).hom ≫ G.map (A ◁ e) ≫ inv pfG ≫
          (inv bs ≫ Q.map ψ) ▷ pM ≫ (β_ pM (Q.obj ωY)).inv) ≫
        (P.map (β_ pM (Q.obj ωY)).hom ≫ inv (pfp (Q.obj ωY)) ≫ bcY.hom.app ωY ▷ M ≫
          Fx.map εY ▷ M ≫ u ▷ M ≫ (λ_ M).hom) := by
  have hinv {W W' : 𝒲} (f : W ⟶ W') :
      P.map (f ▷ pM) ≫ inv (pfp W') = inv (pfp W) ≫ P.map f ▷ M := by
    rw [IsIso.eq_inv_comp, ← reassoc_of% (hpfp f), IsIso.hom_inv_id, Category.comp_id]
  have h₁' : inv pfZ ≫ c.hom.app A ▷ M = c.hom.app (A ⊗ B) ≫ P.map (G.map (A ◁ e)) ≫
      P.map (inv pfG) ≫ inv (pfp (G.obj A)) := by
    rw [IsIso.inv_comp_eq, reassoc_of% h₁, ← P.map_comp_assoc, IsIso.hom_inv_id, P.map_id,
      Category.id_comp, IsIso.hom_inv_id, Category.comp_id]
  have h₂' : bz.hom ▷ M ≫ Fx.map t ▷ M =
      c.hom.app A ▷ M ≫ P.map (inv bs) ▷ M ≫ bcY.hom.app gω ▷ M := by
    have h : bz.hom ≫ Fx.map t = c.hom.app A ≫ P.map (inv bs) ≫ bcY.hom.app gω := by
      rw [← cancel_epi bz.inv, Iso.inv_hom_id_assoc, reassoc_of% h₂]
      simp
    simp only [← comp_whiskerRight, h]
  have hbc : P.map (Q.map ψ) ▷ M ≫ bcY.hom.app ωY ▷ M =
      bcY.hom.app gω ▷ M ≫ Fx.map (Ay.map ψ) ▷ M := by
    simp only [← comp_whiskerRight]
    rw [← Functor.comp_map, bcY.hom.naturality ψ, Functor.comp_map]
  have hc := c.hom.naturality (β_ B A).hom
  dsimp at hc
  rw [← P.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hinv (inv bs ≫ Q.map ψ)), h₃]
  simp only [Functor.map_comp, comp_whiskerRight, Category.assoc]
  rw [reassoc_of% h₂', reassoc_of% h₁', reassoc_of% hc, reassoc_of% hbc]

/-- The trace map of `exceptionalKunnethProdMapTrace` for abstract functors: for `G ⋙ P ≅ P_Z`,
the composite
`G(B ⊗ A) ≅ G(A ⊗ B) ⟶ G(A ⊗ B') ≅ G(A) ⊗ pM ≅ Q(g ω) ⊗ pM ⟶ Q(g g^! ω') ⊗ pM ⟶ Q ω' ⊗ pM ≅
pM ⊗ Q ω'`, with `A = Q_Z (R_Z I)`, `ω' = R_Y I` and `d : g^! ω' ≅ R_Z I`. -/
noncomputable def exceptionalKunnethProdMapTraceAux {𝒱 𝒲 𝒮 𝒴 𝒵 : Type*} [Category 𝒱]
    [Category 𝒲] [Category 𝒮] [Category 𝒴] [Category 𝒵] [MonoidalCategory 𝒱]
    [MonoidalCategory 𝒲] [BraidedCategory 𝒱] [BraidedCategory 𝒲] (G : 𝒱 ⥤ 𝒲) (Q : 𝒴 ⥤ 𝒲)
    (Qz : 𝒵 ⥤ 𝒱) {gl : 𝒵 ⥤ 𝒴} {gr : 𝒴 ⥤ 𝒵} (adjg : gl ⊣ gr) {Ry : 𝒮 ⥤ 𝒴} {Rz : 𝒮 ⥤ 𝒵}
    (I : 𝒮) (d : gr.obj (Ry.obj I) ≅ Rz.obj I) (bs : gl ⋙ Q ⟶ Qz ⋙ G) (ibs : IsIso bs)
    {B B' : 𝒱} (e : B ⟶ B') (pM : 𝒲)
    (pfG : G.obj (Qz.obj (Rz.obj I)) ⊗ pM ⟶ G.obj (Qz.obj (Rz.obj I) ⊗ B')) (ipfG : IsIso pfG) :
    G.obj (B ⊗ Qz.obj (Rz.obj I)) ⟶ pM ⊗ Q.obj (Ry.obj I) :=
  G.map (β_ B (Qz.obj (Rz.obj I))).hom ≫ G.map (Qz.obj (Rz.obj I) ◁ e) ≫ inv pfG ≫
    (inv (bs.app (Rz.obj I)) ≫ Q.map (gl.map d.inv ≫ adjg.counit.app (Ry.obj I))) ▷ pM ≫
    (β_ pM (Q.obj (Ry.obj I))).inv

/-- `exceptionalKunnethAdjoint_comp_prodMap_aux` with the base changes, the composition
isomorphism `Ra_Z! ≅ Rg_! ⋙ Ra_Y!` and the counits given as natural transformations and
adjunctions, so that its instantiation only involves syntactic matches. -/
private lemma exceptionalKunnethAdjoint_comp_prodMap_aux' {𝒳 𝒱 𝒲 𝒮 𝒴 𝒵 : Type*} [Category 𝒳]
    [Category 𝒱] [Category 𝒲] [Category 𝒮] [Category 𝒴] [Category 𝒵] [MonoidalCategory 𝒳]
    [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [BraidedCategory 𝒱] [BraidedCategory 𝒲]
    (PZ : 𝒱 ⥤ 𝒳) (G : 𝒱 ⥤ 𝒲) (P : 𝒲 ⥤ 𝒳) (c : PZ ≅ G ⋙ P) (Fx : 𝒮 ⥤ 𝒳)
    {Ay : 𝒴 ⥤ 𝒮} {Ry : 𝒮 ⥤ 𝒴} (adjY : Ay ⊣ Ry) {Az : 𝒵 ⥤ 𝒮} {Rz : 𝒮 ⥤ 𝒵} (adjZ : Az ⊣ Rz)
    {gl : 𝒵 ⥤ 𝒴} {gr : 𝒴 ⥤ 𝒵} (adjg : gl ⊣ gr) (Q : 𝒴 ⥤ 𝒲) (Qz : 𝒵 ⥤ 𝒱)
    (bcY : Q ⋙ P ≅ Ay ⋙ Fx) (bcZ : Qz ⋙ PZ ≅ Az ⋙ Fx) (bs : gl ⋙ Q ⟶ Qz ⋙ G) (ibs : IsIso bs)
    (cA : Az ≅ gl ⋙ Ay) (I : 𝒮) (d : gr.obj (Ry.obj I) ≅ Rz.obj I)
    (h₃ : adjZ.counit.app I = cA.hom.app (Rz.obj I) ≫
      Ay.map (gl.map d.inv ≫ adjg.counit.app (Ry.obj I)) ≫ adjY.counit.app I)
    (M : 𝒳) {B B' : 𝒱} (e : B ⟶ B') (pM : 𝒲)
    (pfZ : PZ.obj (Qz.obj (Rz.obj I)) ⊗ M ⟶ PZ.obj (Qz.obj (Rz.obj I) ⊗ B)) (ipfZ : IsIso pfZ)
    (pfp : ∀ W : 𝒲, P.obj W ⊗ M ⟶ P.obj (W ⊗ pM)) (ipfp : ∀ W, IsIso (pfp W))
    (hpfp : ∀ {W W' : 𝒲} (f : W ⟶ W'), P.map f ▷ M ≫ pfp W' = pfp W ≫ P.map (f ▷ pM))
    (pfG : G.obj (Qz.obj (Rz.obj I)) ⊗ pM ⟶ G.obj (Qz.obj (Rz.obj I) ⊗ B')) (ipfG : IsIso pfG)
    (h₁ : pfZ ≫ c.hom.app (Qz.obj (Rz.obj I) ⊗ B) ≫
        P.map (G.map (Qz.obj (Rz.obj I) ◁ e)) =
      c.hom.app (Qz.obj (Rz.obj I)) ▷ M ≫ pfp (G.obj (Qz.obj (Rz.obj I))) ≫ P.map pfG)
    (h₂ : bcZ.inv.app (Rz.obj I) ≫ c.hom.app (Qz.obj (Rz.obj I)) =
      Fx.map (cA.hom.app (Rz.obj I)) ≫ bcY.inv.app (gl.obj (Rz.obj I)) ≫
        P.map (bs.app (Rz.obj I)))
    (u : Fx.obj I ⟶ 𝟙_ 𝒳) (aZ : PZ.obj (B ⊗ Qz.obj (Rz.obj I)) ⟶ M)
    (haZ : aZ = PZ.map (β_ B (Qz.obj (Rz.obj I))).hom ≫ inv pfZ ≫ bcZ.hom.app (Rz.obj I) ▷ M ≫
        Fx.map (adjZ.counit.app I) ▷ M ≫ u ▷ M ≫ (λ_ M).hom)
    (aY : P.obj (pM ⊗ Q.obj (Ry.obj I)) ⟶ M)
    (haY : aY = P.map (β_ pM (Q.obj (Ry.obj I))).hom ≫ inv (pfp (Q.obj (Ry.obj I))) ≫
          bcY.hom.app (Ry.obj I) ▷ M ≫ Fx.map (adjY.counit.app I) ▷ M ≫ u ▷ M ≫ (λ_ M).hom) :
    aZ = c.hom.app (B ⊗ Qz.obj (Rz.obj I)) ≫
      P.map (exceptionalKunnethProdMapTraceAux G Q Qz adjg I d bs ibs e pM pfG ipfG) ≫ aY := by
  subst haZ haY
  unfold exceptionalKunnethProdMapTraceAux
  exact exceptionalKunnethAdjoint_comp_prodMap_aux PZ G P c Fx Ay Q bcY M e pM pfZ pfp hpfp pfG h₁
    (bcZ.app (Rz.obj I)) (cA.hom.app (Rz.obj I)) (bs.app (Rz.obj I)) h₂ (adjZ.counit.app I)
    (adjY.counit.app I) (gl.map d.inv ≫ adjg.counit.app (Ry.obj I)) h₃ u

/-- The transposition behind `exceptionalKunnethMap_comp_prodMap`, for abstract adjunctions: if
`a_Z = c ≫ P(φ) ≫ a_Y` with `c : P_Z ≅ G ⋙ P`, then the transpose of `a_Z` along `P_Z ⊣ R_Z` is
the transpose of `φ ≫ (transpose of a_Y)` along `G ⊣ R_G`, followed by the conjugate
`R ⋙ R_G ≅ R_Z` of `c`. -/
private lemma homEquiv_comp_of_eq_aux {𝒳 𝒱 𝒲 : Type*} [Category 𝒳] [Category 𝒱] [Category 𝒲]
    {PZ : 𝒱 ⥤ 𝒳} {RZ : 𝒳 ⥤ 𝒱} {G : 𝒱 ⥤ 𝒲} {RG : 𝒲 ⥤ 𝒱} {P : 𝒲 ⥤ 𝒳} {R : 𝒳 ⥤ 𝒲}
    (adjZ : PZ ⊣ RZ) (adjG : G ⊣ RG) (adjP : P ⊣ R) (c : PZ ≅ G ⋙ P) {K : 𝒱} {L : 𝒲} {M : 𝒳}
    (φ : G.obj K ⟶ L) (aY : P.obj L ⟶ M) (aZ : PZ.obj K ⟶ M)
    (h : aZ = c.hom.app K ≫ P.map φ ≫ aY) :
    adjZ.homEquiv _ _ aZ = adjG.homEquiv _ _ (φ ≫ adjP.homEquiv _ _ aY) ≫
      (conjugateIsoEquiv adjZ (adjG.comp adjP) c.symm).inv.app M := by
  apply (adjZ.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv]
  rw [conjugateEquiv_counit, Adjunction.comp_counit_app]
  have hc := c.hom.naturality ((adjG.homEquiv _ _) (φ ≫ (adjP.homEquiv _ _) aY))
  dsimp at hc
  simp only [Functor.comp_obj]
  rw [reassoc_of% hc, h]
  congr 1
  rw [← P.map_comp_assoc, ← adjG.homEquiv_counit, Equiv.symm_apply_apply, P.map_comp,
    Category.assoc, ← adjP.homEquiv_counit, Equiv.symm_apply_apply]

/-! ### The trace map of `𝟙_X × g` -/

attribute [local irreducible] boundedConstructibleLowerShriek boundedConstructibleUpperStar
  boundedConstructibleUpperShriek

/-! ### The trace map of a cartesian square over a product decomposition -/

section Square

variable {X Y Z W V : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

/-- The trace map `RG_! (Lp_W^* M ⊗ Lq_W^* ω_Z) ⟶ Lp_V^* M ⊗ Lq_V^* ω_Y` of a morphism
`G : W ⟶ V` over `X`, for a cartesian square `q_W ≫ g = G ≫ q_V` with `g : Z ⟶ Y`: the
symmetry, `Lp_W^* ≅ LG^* Lp_V^*`, the inverse of the projection formula for `G`, the inverse of
compact-support base change, `ω_Z ≅ Rg^! ω_Y`, the counit of `Rg_! ⊣ Rg^!` and the symmetry. -/
noncomputable def exceptionalKunnethTraceOfSquare (pW : W ⟶ X) (qW : W ⟶ Z) (pV : V ⟶ X)
    (qV : V ⟶ Y) (G : W ⟶ V) (g : Z ⟶ Y) (sq : IsPullback qW G g qV) (hp : G ≫ pV = pW)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  exceptionalKunnethProdMapTraceAux
    (B := (boundedConstructibleUpperStar _ ℓ pW).obj M)
    (B' := (boundedConstructibleUpperStar _ ℓ G).obj ((boundedConstructibleUpperStar _ ℓ pV).obj M))
    (boundedConstructibleLowerShriek ℓ G) (boundedConstructibleUpperStar _ ℓ qV)
    (boundedConstructibleUpperStar _ ℓ qW) (boundedConstructibleUpperShriekAdjunction ℓ g) _
    (dualizingComplexComp ℓ g) (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    ((boundedConstructibleUpperStarCompOfEq ℓ hp).hom.app M)
    ((boundedConstructibleUpperStar _ ℓ pV).obj M)
    (boundedConstructibleExceptionalProjectionMorphism ℓ G
      ((boundedConstructibleUpperStar _ ℓ qW).obj (dualizingComplex' ℓ Z))
      ((boundedConstructibleUpperStar _ ℓ pV).obj M))
    (isIso_boundedConstructibleExceptionalProjectionMorphism ℓ _ _ _)

-- The instantiation of the abstract chase involves large terms.
/-- **Functoriality of the adjoint of the exceptional Künneth map along a cartesian square**:
for `G : W ⟶ V` over `X` and a cartesian square `q_W ≫ g = G ≫ q_V`, where `(p_W, q_W)` and
`(p_V, q_V)` exhibit `W` and `V` as fibre products over the base point, the morphism
`a_W : Rp_W! (Lp_W^* M ⊗ Lq_W^* ω_Z) ⟶ M` is `Rp_W! ≅ Rp_V! RG_!`, followed by `Rp_V!` of the
trace map and `a_V : Rp_V! (Lp_V^* M ⊗ Lq_V^* ω_Y) ⟶ M`. Here `a_W` and `a_V` are the
composites defining `exceptionalKunnethAdjoint`, with the inverse base changes `bcZ`, `bcY`. -/
theorem exceptionalKunnethAdjoint_comp_of_isPullback (pW : W ⟶ X) (qW : W ⟶ Z) (pV : V ⟶ X)
    (qV : V ⟶ Y) (G : W ⟶ V) (g : Z ⟶ Y) (sq : IsPullback qW G g qV) (hp : G ≫ pV = pW)
    (sqZ : IsPullback qW pW (toPoint Z) (toPoint X))
    (sqY : IsPullback qV pV (toPoint Y) (toPoint X))
    (bcZ : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ qW ⋙
        boundedConstructibleLowerShriek ℓ pW ≅
      boundedConstructibleLowerShriek ℓ (toPoint Z) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))
    (hbcZ : ∀ K, bcZ.inv.app K = (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqZ).app K)
    (bcY : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ qV ⋙
        boundedConstructibleLowerShriek ℓ pV ≅
      boundedConstructibleLowerShriek ℓ (toPoint Y) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))
    (hbcY : ∀ K, bcY.inv.app K = (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY).app K)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (aZ : (boundedConstructibleLowerShriek ℓ pW).obj
      ((boundedConstructibleUpperStar _ ℓ pW).obj M ⊗
        (boundedConstructibleUpperStar _ ℓ qW).obj (dualizingComplex' ℓ Z)) ⟶ M)
    (haZ : aZ = (boundedConstructibleLowerShriek ℓ pW).map (β_ _ _).hom ≫
      inv (boundedConstructibleExceptionalProjectionMorphism ℓ pW
        ((boundedConstructibleUpperStar _ ℓ qW).obj (dualizingComplex' ℓ Z)) M) ≫
      (bcZ.hom.app (dualizingComplex' ℓ Z) ▷ M) ≫
      ((boundedConstructibleUpperStar _ ℓ (toPoint X)).map
        ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z)).counit.app (𝟙_ _)) ▷ M) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv ▷ M) ≫
      (λ_ M).hom)
    (aY : (boundedConstructibleLowerShriek ℓ pV).obj
      ((boundedConstructibleUpperStar _ ℓ pV).obj M ⊗
        (boundedConstructibleUpperStar _ ℓ qV).obj (dualizingComplex' ℓ Y)) ⟶ M)
    (haY : aY = (boundedConstructibleLowerShriek ℓ pV).map (β_ _ _).hom ≫
      inv (boundedConstructibleExceptionalProjectionMorphism ℓ pV
        ((boundedConstructibleUpperStar _ ℓ qV).obj (dualizingComplex' ℓ Y)) M) ≫
      (bcY.hom.app (dualizingComplex' ℓ Y) ▷ M) ≫
      ((boundedConstructibleUpperStar _ ℓ (toPoint X)).map
        ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _)) ▷ M) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv ▷ M) ≫
      (λ_ M).hom) :
    aZ = (boundedConstructibleLowerShriekCompOfEq ℓ hp).hom.app _ ≫
      (boundedConstructibleLowerShriek ℓ pV).map
        (exceptionalKunnethTraceOfSquare ℓ pW qW pV qV G g sq hp M) ≫ aY := by
  have ibs := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have h₁ := boundedConstructibleExceptionalProjectionMorphism_comp_of_eq ℓ hp
    ((boundedConstructibleUpperStar _ ℓ qW).obj (dualizingComplex' ℓ Z)) M
  have h₂ := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert_of_eq ℓ sqZ sq sqY hp
    (comp_toPoint g) (dualizingComplex' ℓ Z)
  simp only [← hbcZ, ← hbcY] at h₂
  have h₃ := boundedConstructibleUpperShriekAdjunction_counit_app_of_eq ℓ (comp_toPoint g)
    _ (dualizingComplexComp ℓ g) (by rw [comp_toPoint]) rfl
  subst haZ haY
  exact exceptionalKunnethAdjoint_comp_prodMap_aux'
    (B := (boundedConstructibleUpperStar _ ℓ pW).obj M)
    (B' := (boundedConstructibleUpperStar _ ℓ G).obj ((boundedConstructibleUpperStar _ ℓ pV).obj M))
    (boundedConstructibleLowerShriek ℓ pW) (boundedConstructibleLowerShriek ℓ G)
    (boundedConstructibleLowerShriek ℓ pV) (boundedConstructibleLowerShriekCompOfEq ℓ hp)
    (boundedConstructibleUpperStar _ ℓ (toPoint X))
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y))
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z))
    (boundedConstructibleUpperShriekAdjunction ℓ g)
    (boundedConstructibleUpperStar _ ℓ qV) (boundedConstructibleUpperStar _ ℓ qW) bcY bcZ
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq) ibs
    (boundedConstructibleLowerShriekCompOfEq ℓ (comp_toPoint g)) _ (dualizingComplexComp ℓ g) h₃ M
    ((boundedConstructibleUpperStarCompOfEq ℓ hp).hom.app M)
    ((boundedConstructibleUpperStar _ ℓ pV).obj M)
    (boundedConstructibleExceptionalProjectionMorphism ℓ pW
      ((boundedConstructibleUpperStar _ ℓ qW).obj (dualizingComplex' ℓ Z)) M)
    (isIso_boundedConstructibleExceptionalProjectionMorphism ℓ _ _ _)
    (fun W ↦ boundedConstructibleExceptionalProjectionMorphism ℓ pV W M)
    (fun W ↦ isIso_boundedConstructibleExceptionalProjectionMorphism ℓ _ W M)
    (fun f ↦ boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ _ f M)
    (boundedConstructibleExceptionalProjectionMorphism ℓ G
      ((boundedConstructibleUpperStar _ ℓ qW).obj (dualizingComplex' ℓ Z))
      ((boundedConstructibleUpperStar _ ℓ pV).obj M))
    (isIso_boundedConstructibleExceptionalProjectionMorphism ℓ _ _ _) h₁ h₂
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv _ rfl _ rfl

end Square

/-! ### The trace map of `𝟙_X × g` -/

section ProdMapSquare

variable {X Y Z : Over (Spec (.of k))}

omit [Fact (ringChar k).Prime] in
variable (X) in
/-- For `g : Z ⟶ Y`, the square `q_Z ≫ g = (𝟙_X × g) ≫ q` of the products with `X` is
cartesian. -/
lemma isPullback_prodMap_id (g : Z ⟶ Y) :
    IsPullback (prod.snd : X ⨯ Z ⟶ Z) (prod.map (𝟙 X) g) g (prod.snd : X ⨯ Y ⟶ Y) := by
  refine IsPullback.of_bot ?_ (by simp) (isPullback_prod_toPoint X Y)
  rw [comp_toPoint, prod.map_fst, Category.comp_id]
  exact isPullback_prod_toPoint X Z

omit [Fact (ringChar k).Prime] in
variable (X) in
/-- `(𝟙_X × g) ≫ p_X = p_X`. -/
lemma prodMap_id_fst (g : Z ⟶ Y) :
    prod.map (𝟙 X) g ≫ (prod.fst : X ⨯ Y ⟶ X) = prod.fst := by
  simp

end ProdMapSquare

section ProdMap

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

variable (X Y) in
/-- The inverse of `prodBaseChangeIso` is compact-support base change. -/
lemma prodBaseChangeIso_inv_app (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (prodBaseChangeIso ℓ X Y).inv.app K =
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (isPullback_prod_toPoint X Y)).app
        K := by
  unfold prodBaseChangeIso
  rfl

/-- The *trace map* `RG_! (M ⊠ ω_Z) ⟶ M ⊠ ω_Y` of `G = 𝟙_X × g`
(`exceptionalKunnethTraceOfSquare` for the cartesian square `q_Z ≫ g = G ≫ q`): the symmetry,
the identification `Lp_Z^* ≅ LG^* Lp^*`, the inverse of the projection formula for `G`, the
inverse of compact-support base change, the identification `ω_Z ≅ Rg^! ω_Y`, the counit of
`Rg_! ⊣ Rg^!` and the symmetry. -/
noncomputable def exceptionalKunnethProdMapTrace (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : Z ⟶ Y) :=
  exceptionalKunnethTraceOfSquare ℓ (prod.fst : X ⨯ Z ⟶ X) prod.snd (prod.fst : X ⨯ Y ⟶ X)
    prod.snd (prod.map (𝟙 X) g) g (isPullback_prodMap_id X g) (prodMap_id_fst X g) M

/-- The trace map of `𝟙_X × g` is that of its cartesian square. -/
lemma exceptionalKunnethProdMapTrace_eq (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : Z ⟶ Y) :
    exceptionalKunnethProdMapTrace ℓ M g =
      exceptionalKunnethTraceOfSquare ℓ (prod.fst : X ⨯ Z ⟶ X) prod.snd (prod.fst : X ⨯ Y ⟶ X)
        prod.snd (prod.map (𝟙 X) g) g (isPullback_prodMap_id X g) (prodMap_id_fst X g) M :=
  rfl

/-- **Functoriality of the exceptional Künneth map in the second factor**, adjoint form: for
`g : Z ⟶ Y` and `G = 𝟙_X × g`, the adjoint `Rp_Z! (M ⊠ ω_Z) ⟶ M` of `α_Z` is
`Rp_Z! ≅ Rp_! RG_!`, followed by `Rp_!` of the trace map `RG_! (M ⊠ ω_Z) ⟶ M ⊠ ω_Y` and the
adjoint of `α_Y`. -/
theorem exceptionalKunnethAdjoint_comp_prodMap (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : Z ⟶ Y) :
    exceptionalKunnethAdjoint ℓ (Y := Z) M =
      (boundedConstructibleLowerShriekCompOfEq ℓ (prodMap_id_fst X g)).hom.app _ ≫
        (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map
          (exceptionalKunnethProdMapTrace ℓ M g) ≫
        exceptionalKunnethAdjoint ℓ (Y := Y) M := by
  rw [exceptionalKunnethProdMapTrace_eq]
  unfold externalProduct
  refine exceptionalKunnethAdjoint_comp_of_isPullback ℓ _ _ _ _ _ g (isPullback_prodMap_id X g)
    (prodMap_id_fst X g) (isPullback_prod_toPoint X Z) (isPullback_prod_toPoint X Y)
    (prodBaseChangeIso ℓ X Z) (prodBaseChangeIso_inv_app ℓ X Z) (prodBaseChangeIso ℓ X Y)
    (prodBaseChangeIso_inv_app ℓ X Y) M _ ?_ _ ?_
  · unfold exceptionalKunnethAdjoint
    simp only [boundedConstructibleExceptionalProjection_app_app]
  · unfold exceptionalKunnethAdjoint
    simp only [boundedConstructibleExceptionalProjection_app_app]

/-- **Functoriality of the exceptional Künneth map in the second factor**: for `g : Z ⟶ Y` and
`G = 𝟙_X × g`, the exceptional Künneth map `α_Z : M ⊠ ω_Z ⟶ Rp_Z^! M` is the transpose along
`RG_! ⊣ RG^!` of the trace map followed by `α_Y`, composed with `RG^! Rp^! M ≅ Rp_Z^! M`. -/
theorem exceptionalKunnethMap_comp_prodMap (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : Z ⟶ Y) :
    exceptionalKunnethMap ℓ (Y := Z) M =
      (boundedConstructibleUpperShriekAdjunction ℓ (prod.map (𝟙 X) g)).homEquiv _ _
          (exceptionalKunnethProdMapTrace ℓ M g ≫ exceptionalKunnethMap ℓ (Y := Y) M) ≫
        (boundedConstructibleUpperShriekCompOfEq ℓ (prodMap_id_fst X g)).inv.app M := by
  rw [boundedConstructibleUpperShriekCompOfEq_eq]
  unfold exceptionalKunnethMap
  exact homEquiv_comp_of_eq_aux
    (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : X ⨯ Z ⟶ X))
    (boundedConstructibleUpperShriekAdjunction ℓ (prod.map (𝟙 X) g))
    (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : X ⨯ Y ⟶ X))
    (boundedConstructibleLowerShriekCompOfEq ℓ (prodMap_id_fst X g))
    (exceptionalKunnethProdMapTrace ℓ M g) (exceptionalKunnethAdjoint ℓ (Y := Y) M)
    (exceptionalKunnethAdjoint ℓ (Y := Z) M) (exceptionalKunnethAdjoint_comp_prodMap ℓ M g)

end ProdMap

end AlgebraicGeometry.ProEtale.CondensedRing
