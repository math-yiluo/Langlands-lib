/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.RefinementOfIsPullback
public import WeilConjectures.Compactification.TriangleOfIsPullback
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Canonical

/-!
# Compact-support base change in a compact support formalism

Let `F` be a `AlgebraicGeometry.CompactSupportFormalism`. For a commutative square of schemes
```
U' --t--> U
|l        |r
Z' --b--> Z
```
the *base change map of the pushforwards* `b^* r_* ⟶ l_* t^*` is the mate of the square
isomorphism `r^* ⋙ t^* ≅ b^* ⋙ l^*` (`CategoryTheory.ExchangeFormalism.pfBaseChange`). The
formalism *satisfies proper base change* (`CompactSupportFormalism.HasProperBaseChange`) if this
map is an isomorphism for every cartesian square with `r` proper.

For a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
a compactification `c = (X ⟶[c.i] c.Z ⟶[c.g] Y)` of `f` and a compactification `c'` of `f'`
lying over it along a morphism `h : c'.Z ⟶ c.Z` with cartesian squares
```
X' --g'--> X
|c'.i      |c.i
c'.Z --h--> c.Z
|c'.g      |c.g
Y' --g---> Y
```
(for instance the base change `c.ofIsPullback sq` of `c`, blueprint
`remark-base-change-compactification--1`), the *compact-support exchange map* (blueprint
`prose-05-31`)

`Ex_! : g^* Rf_!(c) ⟶ Rf'_!(c') g'^*`

is the base change map of the pushforwards for the proper `c.g`, applied after `(c.i)_!`,
composed with the inverse of the base change isomorphism `g'^* ⋙ (c'.i)_! ≅ (c.i)_! ⋙ h^*` of
the extension by zero (`CompactSupportFormalism.shriekBaseChange`). It is an isomorphism when
`F` satisfies base change for the extension by zero and proper base change
(`CompactSupportFormalism.isIso_shriekBaseChange`), and it is natural, the identity for the
identity square, compatible with horizontal pasting and with the comparison isomorphisms along
refinements of compactifications. Computed with the chosen compactifications, it gives the
exchange map `F.lowerShriekBaseChange` of the canonical compactly supported direct images, which
does not depend on the compactification and is compatible with vertical pasting through the
composition isomorphisms.

## Main definitions

- `AlgebraicGeometry.CompactSupportFormalism.HasProperBaseChange`: proper base change.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange`: the exchange map `Ex_!` along
  compactifications.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange`: the exchange map `Ex_!` of
  the canonical compactly supported direct images.

## Main statements

- `AlgebraicGeometry.CompactSupportFormalism.isIso_shriekBaseChange`: `Ex_!` is an isomorphism.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_id`: identity law.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_paste_horiz`: horizontal pasting.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_refinementComparison`:
  compatibility with the comparisons along refinements.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChangeOfIsPullback_shriekIso`:
  compatibility with the comparison isomorphisms.
- `AlgebraicGeometry.CompactSupportFormalism.compIso_shriekBaseChange`: compatibility with the
  composition isomorphisms of triangles of compactifications.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange_eq`: independence of the
  compactification.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange_paste_vert`: vertical pasting.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TwoSquare

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

/-- **Proper base change**: the base change map `b^* r_* ⟶ l_* t^*` of a cartesian square with
`r` proper is an isomorphism (`CategoryTheory.ExchangeFormalism.pfBaseChange`). -/
class HasProperBaseChange : Prop where
  isIso_pfBaseChange {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z}
    {b : Z' ⟶ Z} [IsProper r] (h : IsPullback t l r b) :
    IsIso (F.pfBaseChange t l r b h.w)

section ShriekBaseChange

variable [F.HasBaseChange] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
  {g' : X' ⟶ X}

/-- Blueprint `prose-05-31`: Compact-support exchange map.

**The compact-support exchange map** `Ex_! : g^* Rf_!(c) ⟶ Rf'_!(c') g'^*`, i.e. the natural
transformation `F.shriek c ⋙ g^* ⟶ g'^* ⋙ F.shriek c'`, for a compactification `c` of `f`, a
compactification `c'` of `f'` and a morphism `h : c'.Z ⟶ c.Z` making both squares
```
X' --g'--> X
|c'.i      |c.i
c'.Z --h--> c.Z
|c'.g      |c.g
Y' --g---> Y
```
cartesian. It is the horizontal composite of the inverse of the base change isomorphism
`g'^* ⋙ (c'.i)_! ≅ (c.i)_! ⋙ h^*` of the extension by zero for the upper square with the base
change map `g^* (c.g)_* ⟶ (c'.g)_* h^*` of the pushforwards for the lower square
(`CategoryTheory.ExchangeFormalism.shriekBaseChange`). -/
noncomputable def shriekBaseChange (c : Compactification f) (c' : Compactification f')
    (h : c'.Z ⟶ c.Z) (hi : IsPullback g' c'.i c.i h) (hp : IsPullback h c'.g c.g g) :
    TwoSquare (F.shriek c) (F.pb g') (F.pb g) (F.shriek c') :=
  haveI := HasBaseChange.isIso_baseChange (F := F) hi
  ExchangeFormalism.shriekBaseChange F c.i c.g c'.i c'.g g' h g hi.w hp.w

/-- Blueprint `proposition-composition-base-change-rf-shriek`: Compact-support base change at finite
coefficients, in an abstract compact support formalism.

**The compact-support exchange map is an isomorphism** when the formalism satisfies base change
for the extension by zero and proper base change. -/
instance isIso_shriekBaseChange [F.HasProperBaseChange] (c : Compactification f)
    (c' : Compactification f') (h : c'.Z ⟶ c.Z) (hi : IsPullback g' c'.i c.i h)
    (hp : IsPullback h c'.g c.g g) : IsIso (F.shriekBaseChange c c' h hi hp) := by
  have := HasBaseChange.isIso_baseChange (F := F) hi
  have := HasProperBaseChange.isIso_pfBaseChange (F := F) hp
  dsimp only [shriekBaseChange, ExchangeFormalism.shriekBaseChange, TwoSquare.hComp]
  infer_instance

/-- **The identity law** of the compact-support exchange map: for the identity square, `Ex_!` is
the identity, after inserting the identifications `(𝟙 Y)^* ≅ 𝟭` and `(𝟙 X)^* ≅ 𝟭`.
(blueprint: `proposition-composition-base-change-rf-shriek`) -/
lemma shriekBaseChange_id (c : Compactification f) (hi : IsPullback (𝟙 X) c.i c.i (𝟙 c.Z))
    (hp : IsPullback (𝟙 c.Z) c.g c.g (𝟙 Y)) :
    (F.shriekBaseChange c c (𝟙 c.Z) hi hp) =
      Functor.whiskerLeft (F.shriek c) (F.pbId Y).hom ≫ (Functor.rightUnitor _).hom ≫
        (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (F.pbId X).inv (F.shriek c) := by
  have := HasBaseChange.isIso_baseChange (F := F) hi
  have key : inv (F.baseChange (𝟙 X) c.i c.i (𝟙 c.Z) hi.w) =
      ((TwoSquare.mk (F.sh c.i) (𝟭 _) (𝟭 _) (F.sh c.i)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerRight
          (F.pbId c.Z).hom).whiskerLeft (F.pbId X).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_id_horiz c.i hi.w]
    ext M
    simp [← Functor.map_comp]
  ext K
  simp [shriekBaseChange, ExchangeFormalism.shriekBaseChange, key,
    ExchangeFormalism.pfBaseChange_id_horiz, shriek, ExchangeFormalism.shriek, ← Functor.map_comp]

/-- **Horizontal pasting** of compact-support exchange maps: for two cartesian squares placed
side by side
```
X'' --a'--> X' --b'--> X
|f''        |f'        |f
Y'' --a---> Y' --b---> Y
```
with compactifications `c''`, `c'`, `c` lying over each other along `h₁ : c''.Z ⟶ c'.Z` and
`h₂ : c'.Z ⟶ c.Z`, the exchange map of the outer rectangle along `h₁ ≫ h₂` is the vertical
composite of the two exchange maps, after inserting the composition isomorphisms of the
pullbacks. (blueprint: `proposition-composition-base-change-rf-shriek`) -/
lemma shriekBaseChange_paste_horiz {X'' Y'' : Scheme.{u}} {f'' : X'' ⟶ Y''} {a' : X'' ⟶ X'}
    {a : Y'' ⟶ Y'} {b' : X' ⟶ X} {b : Y' ⟶ Y} (c : Compactification f)
    (c' : Compactification f') (c'' : Compactification f'') (h₁ : c''.Z ⟶ c'.Z)
    (h₂ : c'.Z ⟶ c.Z) (hi₁ : IsPullback a' c''.i c'.i h₁) (hp₁ : IsPullback h₁ c''.g c'.g a)
    (hi₂ : IsPullback b' c'.i c.i h₂) (hp₂ : IsPullback h₂ c'.g c.g b)
    (hi : IsPullback (a' ≫ b') c''.i c.i (h₁ ≫ h₂)) (hp : IsPullback (h₁ ≫ h₂) c''.g c.g (a ≫ b)) :
    F.shriekBaseChange c c'' (h₁ ≫ h₂) hi hp =
      ((F.shriekBaseChange c c' h₂ hi₂ hp₂ ≫ᵥ F.shriekBaseChange c' c'' h₁ hi₁ hp₁).whiskerLeft
        (F.pbComp' a' b' (a' ≫ b') rfl).inv).whiskerRight (F.pbComp' a b (a ≫ b) rfl).hom := by
  have := HasBaseChange.isIso_baseChange (F := F) hi
  have := HasBaseChange.isIso_baseChange (F := F) hi₁
  have := HasBaseChange.isIso_baseChange (F := F) hi₂
  exact ExchangeFormalism.shriekBaseChange_paste_horiz F c.i c.g c'.i c'.g c''.i c''.g a' b' h₁ h₂
    a b hi₁.w hp₁.w hi₂.w hp₂.w hi.w hp.w

/-- **Compatibility with refinements**: the compact-support exchange maps attached to two
compactifications `c`, `d` of `f` (and `c'`, `d'` of `f'`) are intertwined by the comparisons
`Rf_!(d) ⟶ Rf_!(c)` and `Rf'_!(d') ⟶ Rf'_!(c')` along refinements `r : c ⟶ d` and
`r' : c' ⟶ d'` compatible with the maps `c'.Z ⟶ c.Z` and `d'.Z ⟶ d.Z`.
(blueprint: `proposition-composition-base-change-rf-shriek`, independence of the
compactification) -/
lemma shriekBaseChange_refinementComparison {c d : Compactification f}
    {c' d' : Compactification f'} (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (r' : c'.Refinement d') (hr' : IsPullback c'.i (𝟙 X') r'.hom d'.i) (hc : c'.Z ⟶ c.Z)
    (hci : IsPullback g' c'.i c.i hc) (hcp : IsPullback hc c'.g c.g g) (hd : d'.Z ⟶ d.Z)
    (hdi : IsPullback g' d'.i d.i hd) (hdp : IsPullback hd d'.g d.g g)
    (hcomm : hc ≫ r.hom = r'.hom ≫ hd) :
    Functor.whiskerRight (F.refinementComparison r hr) (F.pb g) ≫
        (F.shriekBaseChange c c' hc hci hcp) =
      (F.shriekBaseChange d d' hd hdi hdp) ≫
        Functor.whiskerLeft (F.pb g') (F.refinementComparison r' hr') := by
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  have := HasBaseChange.isIso_baseChange (F := F) hr'.flip
  have := HasBaseChange.isIso_baseChange (F := F) hci
  have := HasBaseChange.isIso_baseChange (F := F) hdi
  exact ExchangeFormalism.shriekBaseChange_refinementComparison F c.i c.g d.i d.g c'.i c'.g d'.i
    d'.g g' g r.hom hr.flip.w r.hom_g r'.hom hr'.flip.w r'.hom_g hc hci.w hcp.w hd hdi.w hdp.w
    hcomm

end ShriekBaseChange

section Composition

variable [F.HasProperExchange]

/-- **The compact-support exchange maps and the composition isomorphisms.** Let `T` be a
triangle of compactifications of `(f, g)` and `T'` a triangle of compactifications of
`(f', g')` lying over it along `a : T'.cf.Z ⟶ T.cf.Z`, `c : T'.cg.Z ⟶ T.cg.Z` and
`b : T'.cfg.Z ⟶ T.cfg.Z`, with all the relevant squares cartesian. Then the exchange map of the
composite is the horizontal composite of the exchange maps, through the composition
isomorphisms `F.compIso T` and `F.compIso T'`. (blueprint:
`proposition-composition-base-change-rf-shriek`, `proposition-composition-base-change-rf-shriek`) -/
theorem compIso_shriekBaseChange {X Y S X' Y' S' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ S'} {gX : X' ⟶ X} {gY : Y' ⟶ Y} {gS : S' ⟶ S}
    (T : Compactification.Triangle f g) (T' : Compactification.Triangle f' g')
    (a : T'.cf.Z ⟶ T.cf.Z) (c : T'.cg.Z ⟶ T.cg.Z) (b : T'.cfg.Z ⟶ T.cfg.Z)
    (hfi : IsPullback gX T'.cf.i T.cf.i a) (hfp : IsPullback a T'.cf.g T.cf.g gY)
    (hgi : IsPullback gY T'.cg.i T.cg.i c) (hgp : IsPullback c T'.cg.g T.cg.g gS)
    (hfgi : IsPullback gX T'.cfg.i T.cfg.i b) (hfgp : IsPullback b T'.cfg.g T.cfg.g gS)
    (hq : IsPullback a T'.q T.q b) (hp : b ≫ T.p = T'.p ≫ c) :
    Functor.whiskerRight (F.compIso T).hom (F.pb gS) ≫
        (F.shriekBaseChange T.cfg T'.cfg b hfgi hfgp) =
      (F.shriekBaseChange T.cf T'.cf a hfi hfp ≫ₕ
          F.shriekBaseChange T.cg T'.cg c hgi hgp) ≫
        Functor.whiskerLeft (F.pb gX) (F.compIso T').hom := by
  have := HasBaseChange.isIso_baseChange (F := F) T.isPullback
  have := HasProperExchange.isIso_exchange (F := F) T.isPullback
  have := HasBaseChange.isIso_baseChange (F := F) T'.isPullback
  have := HasProperExchange.isIso_exchange (F := F) T'.isPullback
  have := HasBaseChange.isIso_baseChange (F := F) hfi
  have := HasBaseChange.isIso_baseChange (F := F) hgi
  have := HasBaseChange.isIso_baseChange (F := F) hfgi
  have := HasBaseChange.isIso_baseChange (F := F) hq
  exact ExchangeFormalism.compIso_shriekBaseChange F T.toShriekTriangle T'.toShriekTriangle a c b
    hfi.w hfp.w hgi.w hgp.w hfgi.w hfgp.w hq.w hp

end Composition

section Canonical

variable [F.HasProperExchange] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- The compact-support exchange map `Ex_!` along a compactification `c` of `f` and its base
change `c.ofIsPullback sq` (blueprint `remark-base-change-compactification--1`). -/
noncomputable abbrev shriekBaseChangeOfIsPullback (sq : IsPullback g' f' f g)
    (c : Compactification f) :
    TwoSquare (F.shriek c) (F.pb g') (F.pb g) (F.shriek (c.ofIsPullback sq)) :=
  F.shriekBaseChange c (c.ofIsPullback sq) (pullback.fst c.g g)
    (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip

/-- **The compact-support exchange map of the canonical compactly supported direct images**
`Ex_! : g^* Rf_! ⟶ Rf'_! g'^*`: the exchange map along the chosen compactification of `f` and its
base change, followed by the comparison isomorphism with the chosen compactification of `f'`.
(blueprint: `prose-05-31`) -/
noncomputable def lowerShriekBaseChange [HasCompactification f] [HasCompactification f']
    [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    TwoSquare (F.lowerShriek f) (F.pb g') (F.pb g) (F.lowerShriek f') :=
  (F.shriekBaseChangeOfIsPullback sq (HasCompactification.compactification f)).whiskerBottom
    (F.shriekIso _ (HasCompactification.compactification f')).hom

instance isIso_lowerShriekBaseChange [F.HasProperBaseChange] [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (F.lowerShriekBaseChange sq) := by
  dsimp only [lowerShriekBaseChange, TwoSquare.whiskerBottom]
  infer_instance

/-- **Compatibility with the comparison isomorphisms**: the compact-support exchange maps along
two compactifications `c` and `d` of `f` and their base changes are intertwined by the comparison
isomorphisms `F.shriekIso c d` and `F.shriekIso (c.ofIsPullback sq) (d.ofIsPullback sq)`.
(blueprint: `proposition-composition-base-change-rf-shriek`, independence of the
compactification) -/
lemma shriekBaseChangeOfIsPullback_shriekIso [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c d : Compactification f) :
    Functor.whiskerRight (F.shriekIso c d).hom (F.pb g) ≫
        (F.shriekBaseChangeOfIsPullback sq d) =
      (F.shriekBaseChangeOfIsPullback sq c) ≫
        Functor.whiskerLeft (F.pb g')
          (F.shriekIso (c.ofIsPullback sq) (d.ofIsPullback sq)).hom := by
  have hr₀ := Compactification.isPullback_infFst c d
  have hr := Compactification.isPullback_infSnd c d
  have hr₀' := (Compactification.infFst c d).isPullback_ofIsPullback sq hr₀
  have hr' := (Compactification.infSnd c d).isPullback_ofIsPullback sq hr
  have h₀ := F.shriekBaseChange_refinementComparison (Compactification.infFst c d) hr₀
    ((Compactification.infFst c d).ofIsPullback sq) hr₀' (pullback.fst (c.inf d).g g)
    ((c.inf d).isPullback_i_ofIsPullback sq) ((c.inf d).isPullback_g_ofIsPullback sq).flip
    (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip
    (Compactification.Refinement.ofIsPullback_hom_fst sq _).symm
  have h₁ := F.shriekBaseChange_refinementComparison (Compactification.infSnd c d) hr
    ((Compactification.infSnd c d).ofIsPullback sq) hr' (pullback.fst (c.inf d).g g)
    ((c.inf d).isPullback_i_ofIsPullback sq) ((c.inf d).isPullback_g_ofIsPullback sq).flip
    (pullback.fst d.g g) (d.isPullback_i_ofIsPullback sq) (d.isPullback_g_ofIsPullback sq).flip
    (Compactification.Refinement.ofIsPullback_hom_fst sq _).symm
  rw [F.shriekIso_eq _ _ hr₀' hr', F.shriekIso_eq _ _ hr₀ hr]
  ext K
  have h₀' := congr_app h₀ K
  have h₁' := congr_app h₁ K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₀' h₁'
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
  dsimp only [shriekBaseChangeOfIsPullback]
  rw [← cancel_mono ((F.refinementComparison _ hr').app ((F.pb g').obj K))]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₀', ← h₁', ← Functor.map_comp_assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

/-- **Independence of the compactification**: the exchange map of the canonical compactly
supported direct images is computed by any compactification `c` of `f` and its base change, up
to the comparison isomorphisms `F.shriekIso`. (blueprint:
`proposition-composition-base-change-rf-shriek`, `proposition-composition-base-change-rf-shriek`) -/
theorem lowerShriekBaseChange_eq [HasCompactification f] [HasCompactification f']
    [QuasiCompact f] [QuasiCompact f'] (sq : IsPullback g' f' f g) (c : Compactification f) :
    F.lowerShriekBaseChange sq =
      ((F.shriekBaseChangeOfIsPullback sq c).whiskerTop
        (F.shriekIso (HasCompactification.compactification f) c).hom).whiskerBottom
        (F.shriekIso _ (HasCompactification.compactification f')).hom := by
  have h := F.shriekBaseChangeOfIsPullback_shriekIso sq
    (HasCompactification.compactification f) c
  rw [← F.shriekIso_trans _ ((HasCompactification.compactification f).ofIsPullback sq)
    (HasCompactification.compactification f'),
    ← F.shriekIso_symm ((HasCompactification.compactification f).ofIsPullback sq)]
  ext K
  have h' := congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h'
  simp only [lowerShriekBaseChange, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
    Iso.symm_hom, Category.assoc]
  rw [reassoc_of% h', Iso.hom_inv_id_app_assoc]

/-- **Vertical pasting** of compact-support exchange maps: for two cartesian squares placed one
above the other
```
X' --gX--> X
|f₁'       |f₁
Y' --gY--> Y
|f₂'       |f₂
S' --gS--> S
```
the exchange map of the outer rectangle is the horizontal composite of the two exchange maps,
after inserting the composition isomorphisms `Rf₁_! ⋙ Rf₂_! ≅ R(f₁ ≫ f₂)_!`.
(blueprint: `proposition-composition-base-change-rf-shriek`) -/
theorem lowerShriekBaseChange_paste_vert {S S' : Scheme.{u}} {f₁ : X ⟶ Y} {f₂ : Y ⟶ S}
    {f₁' : X' ⟶ Y'} {f₂' : Y' ⟶ S'} {gX : X' ⟶ X} {gY : Y' ⟶ Y} {gS : S' ⟶ S}
    [HasCompactification f₁] [HasCompactification f₂] [HasCompactification (f₁ ≫ f₂)]
    [HasCompactification f₁'] [HasCompactification f₂'] [HasCompactification (f₁' ≫ f₂')]
    [QuasiCompact (f₁ ≫ f₂)] [QuasiCompact f₁'] [QuasiCompact f₂'] [QuasiCompact (f₁' ≫ f₂')]
    (sq₁ : IsPullback gX f₁' f₁ gY) (sq₂ : IsPullback gY f₂' f₂ gS)
    (sq : IsPullback gX (f₁' ≫ f₂') (f₁ ≫ f₂) gS) :
    F.lowerShriekBaseChange sq =
      ((F.lowerShriekBaseChange sq₁ ≫ₕ F.lowerShriekBaseChange sq₂).whiskerTop
        (F.lowerShriekCompIso f₁ f₂).inv).whiskerBottom (F.lowerShriekCompIso f₁' f₂').hom := by
  have : QuasiCompact f₁ := .of_comp f₁ f₂
  let T := Compactification.Triangle.ofHasCompactification f₁ f₂
  have hKey : Functor.whiskerRight (F.compIso T).hom (F.pb gS) ≫
      (F.shriekBaseChangeOfIsPullback sq T.cfg) =
      (F.shriekBaseChangeOfIsPullback sq₁ T.cf ≫ₕ
        F.shriekBaseChangeOfIsPullback sq₂ T.cg) ≫
        Functor.whiskerLeft (F.pb gX) (F.compIso (T.ofIsPullback sq₁ sq₂ sq)).hom :=
    F.compIso_shriekBaseChange T (T.ofIsPullback sq₁ sq₂ sq)
      (pullback.fst T.cf.g gY) (pullback.fst T.cg.g gS) (pullback.fst T.cfg.g gS)
      (T.cf.isPullback_i_ofIsPullback sq₁) (T.cf.isPullback_g_ofIsPullback sq₁).flip
      (T.cg.isPullback_i_ofIsPullback sq₂) (T.cg.isPullback_g_ofIsPullback sq₂).flip
      (T.cfg.isPullback_i_ofIsPullback sq) (T.cfg.isPullback_g_ofIsPullback sq).flip
      (T.isPullback_baseChangeQ sq₂) T.baseChangeP_fst.symm
  have hE₂ : F.lowerShriekBaseChange sq₂ =
      (F.shriekBaseChangeOfIsPullback sq₂ T.cg).whiskerBottom
        (F.shriekIso (T.cg.ofIsPullback sq₂) (HasCompactification.compactification f₂')).hom :=
    rfl
  have hCI : (F.lowerShriekCompIso f₁ f₂).hom =
      Functor.whiskerRight (F.shriekIso (HasCompactification.compactification f₁) T.cf).hom _ ≫
        (F.compIso T).hom ≫
        (F.shriekIso T.cfg (HasCompactification.compactification (f₁ ≫ f₂))).hom :=
    rfl
  have hCI' : (F.lowerShriekCompIso f₁' f₂').hom =
      NatTrans.hcomp
        (F.shriekIso (T.cf.ofIsPullback sq₁) (HasCompactification.compactification f₁')).inv
        (F.shriekIso (T.cg.ofIsPullback sq₂) (HasCompactification.compactification f₂')).inv ≫
      (F.compIso (T.ofIsPullback sq₁ sq₂ sq)).hom ≫
      (F.shriekIso (T.cfg.ofIsPullback sq)
        (HasCompactification.compactification (f₁' ≫ f₂'))).hom := by
    rw [← Iso.symm_hom, ← Iso.symm_hom, F.shriekIso_symm, F.shriekIso_symm]
    exact F.lowerShriekCompIso_hom_eq (T.ofIsPullback sq₁ sq₂ sq)
  rw [F.lowerShriekBaseChange_eq sq₁ T.cf, F.lowerShriekBaseChange_eq sq T.cfg, hE₂,
    ← F.shriekIso_symm T.cfg]
  ext K
  have hK := congr_app hKey K
  rw [← cancel_epi ((F.pb gS).map ((F.lowerShriekCompIso f₁ f₂).hom.app K))]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc, Functor.comp_obj] at hK ⊢
  have hcancel : (F.pb gS).map ((F.lowerShriekCompIso f₁ f₂).hom.app K) ≫
      (F.pb gS).map ((F.lowerShriekCompIso f₁ f₂).inv.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hcancel, hCI, hCI']
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  have hB := (F.shriekBaseChangeOfIsPullback sq₂ T.cg).naturality
    ((F.shriekIso (HasCompactification.compactification f₁) T.cf).hom.app K)
  simp only [Functor.comp_map] at hB
  have hI : (F.shriekIso (T.cg.ofIsPullback sq₂) (HasCompactification.compactification f₂')).hom.app
        ((F.pb gY).obj ((F.lowerShriek f₁).obj K)) ≫
      (F.lowerShriek f₂').map
        ((F.pb gY).map ((F.shriekIso (HasCompactification.compactification f₁) T.cf).hom.app K)) ≫
      (F.lowerShriek f₂').map ((F.shriekBaseChangeOfIsPullback sq₁ T.cf).app K) ≫
      (F.lowerShriek f₂').map ((F.shriekIso (T.cf.ofIsPullback sq₁)
        (HasCompactification.compactification f₁')).hom.app ((F.pb gX).obj K)) ≫
      (F.shriekIso (T.cg.ofIsPullback sq₂) (HasCompactification.compactification f₂')).inv.app
        ((F.shriek (HasCompactification.compactification f₁')).obj ((F.pb gX).obj K)) =
      (F.shriek (T.cg.ofIsPullback sq₂)).map
        ((F.pb gY).map ((F.shriekIso (HasCompactification.compactification f₁) T.cf).hom.app K)) ≫
      (F.shriek (T.cg.ofIsPullback sq₂)).map
        ((F.shriekBaseChangeOfIsPullback sq₁ T.cf).app K) ≫
      (F.shriek (T.cg.ofIsPullback sq₂)).map ((F.shriekIso (T.cf.ofIsPullback sq₁)
        (HasCompactification.compactification f₁')).hom.app ((F.pb gX).obj K)) := by
    simp only [← Functor.map_comp, ← Functor.map_comp_assoc]
    rw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [← Functor.map_comp_assoc (F.pb gS)
      ((F.shriekIso T.cfg (HasCompactification.compactification (f₁ ≫ f₂))).hom.app K),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hK,
    reassoc_of% hB, reassoc_of% hI,
    ← Functor.map_comp_assoc (F.shriek (T.cg.ofIsPullback sq₂))
      ((F.shriekIso (T.cf.ofIsPullback sq₁)
        (HasCompactification.compactification f₁')).hom.app ((F.pb gX).obj K)),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end Canonical

end AlgebraicGeometry.CompactSupportFormalism
