/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.PullbackFamily
public import WeilConjectures.TraceFormula.ShriekTraceFunction

/-!

# Iterated structure isomorphisms and stalks of pullbacks of algebras

For a family of pullbacks `P` with composition isomorphisms `c` (`CategoryTheory.PullbackAssoc`),
this file proves the two coherences behind the pullback of Weil sheaves:

- `CategoryTheory.Iso.powSuccStr_pullbackFamilyComparison`: the iterated structure isomorphism of
  the pullback of an algebra along `g` with `e_W ≫ g = g ≫ e_X` is the pullback of the iterated
  structure isomorphism, along `e_W^{n+1}` and `e_X^{n+1}`;
- `Endofunctor.IsoAlgebra.nonempty_stalk_overPowSucc_overPullback_iso`: the composition
  isomorphism `P w (P g F) ≅ P (w ≫ g) F` is an isomorphism between the stalk at `w` of the
  `(n + 1)`-st iterate of the pullback of `F`, and the stalk at `w ≫ g` of the `(n + 1)`-st iterate
  of `F` (`Endofunctor.IsoAlgebra.nonempty_obj_obj_iso_of_eq` is the form used for concrete
  instances, whose functors are given through equations);
- `Endofunctor.IsoAlgebra.overPowFunctor_succ`: for identity isomorphisms `P 𝟙 ≅ 𝟭` compatible
  with the composition isomorphisms, the iterates with `Iso.powStr` at `n + 1` are the iterates
  with `Iso.powSuccStr` at `n`.

## Implementation notes

The statements are generic in the family of pullbacks. Instantiated directly for the pullbacks
of module objects, the elaborator and the kernel unfold the pullbacks while comparing terms that
are equal only up to unfolding; in the generic setting these comparisons are cheap.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : C → Type*} [∀ X, Category (D X)]
  (P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X)
  (c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)

variable {P c}


/-- The key identity behind `Iso.powSuccStr_pullbackFamilyComparison`: for `E ≫ g = g ≫ E'` and
`e ≫ g = g ≫ e'`, the two ways of identifying `P (E ≫ e) (P g F)` with
`P g (P E' (P e' F))` agree. -/
@[reassoc]
lemma pullbackFamilyComparison_comp_aux (hc : PullbackAssoc P c) {W X : C} (g : W ⟶ X)
    (E e : W ⟶ W) (E' e' : X ⟶ X) (hE : E ≫ g = g ≫ E') (he : e ≫ g = g ≫ e') (F : D X) :
    (c E e).hom.app ((P g).obj F) ≫ (P E).map ((c e g).inv.app F) ≫
        (P E).map (eqToHom (by rw [he])) ≫ (P E).map ((c g e').hom.app F) ≫
        (c E g).inv.app ((P e').obj F) ≫ eqToHom (by rw [hE]) ≫
        (c g E').hom.app ((P e').obj F) =
      (c (E ≫ e) g).inv.app F ≫
        eqToHom (by rw [Category.assoc, he, ← Category.assoc, hE, Category.assoc]) ≫
        (c g (E' ≫ e')).hom.app F ≫ (P g).map ((c E' e').hom.app F) := by
  rw [← cancel_epi ((c (E ≫ e) g).hom.app F), Iso.hom_inv_id_app_assoc,
    reassoc_of% (hc.hom_app E e g F), ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp, eqToHom_map, pullbackComp_hom_app_comp_eqToHom_right_assoc (c := c) E he,
    hc.hom_app_comp_map_hom_app_assoc, Iso.hom_inv_id_app_assoc,
    pullbackComp_hom_app_comp_eqToHom_left_assoc (c := c) hE,
    hc.hom_app_comp_map_hom_app]
  simp only [eqToHom_trans_assoc]

/-- **The iterated structure isomorphism of a pullback**: for `g : W ⟶ X` with
`e_W ≫ g = g ≫ e_X` and `φ : P e_X F ≅ F`, the iterated structure isomorphism of `P g F` with
`P e_W (P g F) ≅ P g (P e_X F) ≅ P g F` is the pullback, along `e_W^{n+1}` and `e_X^{n+1}`, of
the iterated structure isomorphism of `F`. -/
theorem Iso.powSuccStr_pullbackFamilyComparison (hc : PullbackAssoc P c) {W X : C} (eW : W ≅ W)
    (eX : X ≅ X) (g : W ⟶ X) (hg : eW.hom ≫ g = g ≫ eX.hom) {F : D X}
    (φ : (P eX.hom).obj F ≅ F) (n : ℕ) :
    (eW.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f')
        ((pullbackFamilyComparison (c := c) g eW.hom eX.hom hg).app F ≪≫ (P g).mapIso φ) n).hom =
      (pullbackFamilyComparison (c := c) g (eW.pow (n + 1)).hom (eX.pow (n + 1)).hom
          (Iso.pow_hom_comp_eq_comp_pow_hom eW eX hg n)).hom.app F ≫
        (P g).map (eX.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f') φ n).hom := by
  induction n with
  | zero =>
    have key : ∀ {E E' : W ⟶ W} {e e' : X ⟶ X} (hE : E = E') (he : e = e')
        (s : E ≫ g = g ≫ e) (s' : E' ≫ g = g ≫ e'),
        eqToHom (congrArg (fun t ↦ (P t).obj ((P g).obj F)) hE) ≫
            (pullbackFamilyComparison (c := c) g E' e' s').hom.app F =
          (pullbackFamilyComparison (c := c) g E e s).hom.app F ≫
            (P g).map (eqToHom (congrArg (fun t ↦ (P t).obj F) he)) := by
      rintro E _ e _ rfl rfl s s'
      simp
    rw [Iso.powSuccStr_zero, Iso.powSuccStr_zero]
    simp only [Iso.trans_hom, eqToIso.hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
    exact (reassoc_of% key (Category.id_comp eW.hom) (Category.id_comp eX.hom) _ hg) _
  | succ n ih =>
    have hn := Iso.pow_hom_comp_eq_comp_pow_hom eW eX hg n
    change (c (eW.pow (n + 1)).hom eW.hom).hom.app ((P g).obj F) ≫
        (P (eW.pow (n + 1)).hom).map
          ((pullbackFamilyComparison (c := c) g eW.hom eX.hom hg).hom.app F ≫ (P g).map φ.hom) ≫
        (eW.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f')
          ((pullbackFamilyComparison (c := c) g eW.hom eX.hom hg).app F ≪≫ (P g).mapIso φ) n).hom =
      (pullbackFamilyComparison (c := c) g ((eW.pow (n + 1)).hom ≫ eW.hom)
          ((eX.pow (n + 1)).hom ≫ eX.hom)
          (by rw [Category.assoc, hg, ← Category.assoc, hn, Category.assoc])).hom.app F ≫
        (P g).map ((c (eX.pow (n + 1)).hom eX.hom).hom.app F ≫
          (P (eX.pow (n + 1)).hom).map φ.hom ≫
          (eX.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f') φ n).hom)
    rw [ih]
    simp only [pullbackFamilyComparison_hom_app, Functor.map_comp, Category.assoc]
    have nat₁ := (c (eW.pow (n + 1)).hom g).inv.naturality φ.hom
    have nat₂ := (c g (eX.pow (n + 1)).hom).hom.naturality φ.hom
    simp only [Functor.comp_map] at nat₁ nat₂
    rw [reassoc_of% nat₁, map_comp_eqToHom_of_eq_assoc hn, reassoc_of% nat₂,
      pullbackFamilyComparison_comp_aux_assoc hc g _ _ _ _ hn hg F]

/-- A version of `Iso.powSuccStr_pullbackFamilyComparison` for a structure isomorphism `ψ` of
`P g F`
given
through its underlying morphism. -/
theorem Iso.powSuccStr_hom_eq_of_hom_eq (hc : PullbackAssoc P c) {W X : C} (eW : W ≅ W)
    (eX : X ≅ X) (g : W ⟶ X) (hg : eW.hom ≫ g = g ≫ eX.hom) {F : D X}
    (φ : (P eX.hom).obj F ≅ F) (ψ : (P eW.hom).obj ((P g).obj F) ≅ (P g).obj F)
    (hψ : ψ.hom =
      (pullbackFamilyComparison (c := c) g eW.hom eX.hom hg).hom.app F ≫ (P g).map φ.hom)
    (n : ℕ) :
    (eW.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f') ψ n).hom =
      (pullbackFamilyComparison (c := c) g (eW.pow (n + 1)).hom (eX.pow (n + 1)).hom
          (Iso.pow_hom_comp_eq_comp_pow_hom eW eX hg n)).hom.app F ≫
        (P g).map (eX.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f') φ n).hom := by
  obtain rfl : ψ = (pullbackFamilyComparison (c := c) g eW.hom eX.hom hg).app F ≪≫ (P g).mapIso φ :=
    Iso.ext hψ
  exact Iso.powSuccStr_pullbackFamilyComparison hc eW eX g hg φ n


/-! ### Algebras over the overcategory -/

section Over

variable {T : C}

/-- A family of pullbacks on `C` induces one on `Over T`, through the underlying morphisms. -/
lemma PullbackAssoc.over (hc : PullbackAssoc P c) :
    PullbackAssoc (C := Over T) (D := fun V ↦ D V.left)
      (fun {X Y : Over T} (f : X ⟶ Y) ↦ P f.left)
      (fun {X Y Z : Over T} (f : X ⟶ Y) (g : Y ⟶ Z) ↦ c f.left g.left) :=
  fun f g h ↦ hc f.left g.left h.left

variable (c) in
/-- The pullback of algebras `(F, φ : P e_X F ≅ F)` along `g : W ⟶ X` over `T` with
`e_W ≫ g = g ≫ e_X`: `P g F` with `P e_W (P g F) ≅ P g (P e_X F) ≅ P g F`. -/
noncomputable def Endofunctor.IsoAlgebra.overPullback {X W : Over T} (eX : X ≅ X) (eW : W ≅ W)
    {g : W ⟶ X}
    (hg : eW.hom ≫ g = g ≫ eX.hom) :
    Endofunctor.IsoAlgebra (P eX.hom.left) ⥤ Endofunctor.IsoAlgebra (P eW.hom.left) :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (pullbackFamilyComparison (c := c) g.left eW.hom.left eX.hom.left
      (Over.left_comp_left_eq_of_comp_eq hg))

variable (c) in
/-- An algebra `(F, φ)` for `P e` as an algebra for `P e^{n+1}`, with the iterated structure
isomorphism. -/
noncomputable def Endofunctor.IsoAlgebra.overPowSucc {X : Over T} (e : X ≅ X) (n : ℕ)
    (G : Endofunctor.IsoAlgebra (P e.hom.left)) :
    Endofunctor.IsoAlgebra (P (e.pow (n + 1)).hom.left) :=
  Endofunctor.IsoAlgebra.mk G.carrier
    (e.powSuccStr (fun f ↦ P f.left) (fun f f' ↦ c f.left f'.left) G.str n)

/-- The underlying morphism of `eqToHom` between algebras is `eqToHom` of the carriers. -/
lemma Endofunctor.IsoAlgebra.eqToHom_hom_f {F : C ⥤ C} {A B : Endofunctor.IsoAlgebra F}
    (h : A = B) :
    (eqToHom h).hom.f = eqToHom (congrArg Endofunctor.IsoAlgebra.carrier h) := by
  subst h
  rfl

variable (c) in
/-- The stalk of algebras at a point `x : S ⟶ V` with `x ≫ e = s ≫ x`, for `τ : P s ≅ 𝟭`. -/
noncomputable def Endofunctor.IsoAlgebra.stalk {S : C} {s : S ⟶ S} (τ : P s ≅ 𝟭 (D S)) {V : C}
    (x : S ⟶ V)
    (e : V ⟶ V)
    (h : x ≫ e = s ≫ x) :
    Endofunctor.IsoAlgebra (P e) ⥤ Endofunctor.IsoAlgebra (𝟭 (D S)) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (pullbackFamilyStalkComparison (c := c) τ x e h)

variable (c) in
/-- An algebra for `P e` as an algebra for `P e^{n+1}` (`Endofunctor.IsoAlgebra.overPowSucc`), as a
functor. -/
noncomputable def Endofunctor.IsoAlgebra.overPowSuccFunctor {X : Over T} (e : X ≅ X) (n : ℕ) :
    Endofunctor.IsoAlgebra (P e.hom.left) ⥤
      Endofunctor.IsoAlgebra (P (e.pow (n + 1)).hom.left) where
  obj G := Endofunctor.IsoAlgebra.overPowSucc c e n G
  map {G H} φ := Endofunctor.IsoAlgebra.mkHom φ.hom.f
    (e.powSuccStr_hom_naturality (fun f ↦ P f.left) (fun f f' ↦ c f.left f'.left) (φ := G.str)
      (ψ := H.str) φ.hom.f φ.hom.h n)
  map_id _ := Endofunctor.IsoAlgebra.mkHom_id _
  map_comp _ _ := Endofunctor.IsoAlgebra.mkHom_comp _ _ _ _ _

variable (c) in
/-- An algebra `(F, φ)` for `P e` as an algebra for `P eᵐ`, with the iterated structure
isomorphism `Iso.powStr` for identity isomorphisms `ι Y : P 𝟙 ≅ 𝟭`, as a functor. -/
noncomputable def Endofunctor.IsoAlgebra.overPowFunctor (ι : ∀ Y : C, P (𝟙 Y) ≅ 𝟭 (D Y))
    {X : Over T} (e : X ≅ X) (m : ℕ) :
    Endofunctor.IsoAlgebra (P e.hom.left) ⥤ Endofunctor.IsoAlgebra (P (e.pow m).hom.left) where
  obj G := Endofunctor.IsoAlgebra.mk G.carrier
    (e.powStr (fun f ↦ P f.left) (ι X.left) (fun f f' ↦ c f.left f'.left) G.str m)
  map {G H} φ := Endofunctor.IsoAlgebra.mkHom φ.hom.f
    (e.powStr_hom_naturality (fun f ↦ P f.left) (ι X.left) (fun f f' ↦ c f.left f'.left)
      (φ := G.str) (ψ := H.str) φ.hom.f φ.hom.h m)
  map_id _ := Endofunctor.IsoAlgebra.mkHom_id _
  map_comp _ _ := Endofunctor.IsoAlgebra.mkHom_comp _ _ _ _ _

/-- For identity isomorphisms `ι` compatible with the composition isomorphisms, the
`(n + 1)`-st iterate with `Iso.powStr` is the `(n + 1)`-st iterate with `Iso.powSuccStr`. -/
theorem Endofunctor.IsoAlgebra.overPowFunctor_succ (ι : ∀ Y : C, P (𝟙 Y) ≅ 𝟭 (D Y))
    (hι : ∀ {Y Z : C} (t : Y ⟶ Z), c (𝟙 Y) t ≪≫ Functor.isoWhiskerLeft (P t) (ι Y) ≪≫
      Functor.rightUnitor (P t) = eqToIso (congrArg P (Category.id_comp t)))
    {X : Over T} (e : X ≅ X) (n : ℕ) :
    Endofunctor.IsoAlgebra.overPowFunctor c ι e (n + 1) =
      Endofunctor.IsoAlgebra.overPowSuccFunctor c e n := by
  have h (G : Endofunctor.IsoAlgebra (P e.hom.left)) :
      e.powStr (fun f ↦ P f.left) (ι X.left) (fun f f' ↦ c f.left f'.left) G.str (n + 1) =
        e.powSuccStr (fun f ↦ P f.left) (fun f f' ↦ c f.left f'.left) G.str n :=
    e.powStr_succ_eq_powSuccStr (fun f ↦ P f.left) (ι X.left) (fun f f' ↦ c f.left f'.left) G.str
      (hι e.hom.left) n
  refine Functor.ext (fun G ↦ congrArg (Endofunctor.IsoAlgebra.mk G.carrier) (h G))
    fun G H φ ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext ?_)
  rw [Endofunctor.IsoAlgebra.comp_hom_f, Endofunctor.IsoAlgebra.comp_hom_f,
    Endofunctor.IsoAlgebra.eqToHom_hom_f, Endofunctor.IsoAlgebra.eqToHom_hom_f]
  change φ.hom.f = 𝟙 G.carrier ≫ φ.hom.f ≫ 𝟙 H.carrier
  rw [Category.id_comp, Category.comp_id]

variable (c) in
/-- The stalk at a point `x` with `x ≫ e^{n+1} = s ≫ x` of algebras for `P e`, with their
`(n + 1)`-st structure isomorphisms. -/
noncomputable def Endofunctor.IsoAlgebra.frobeniusStalkFunctor {S : C} {s : S ⟶ S}
    (τ : P s ≅ 𝟭 (D S))
    {V : Over T} (e : V ≅ V) (n : ℕ) (x : S ⟶ V.left) (hx : x ≫ (e.pow (n + 1)).hom.left = s ≫ x) :
    Endofunctor.IsoAlgebra (P e.hom.left) ⥤ Endofunctor.IsoAlgebra (𝟭 (D S)) :=
  Endofunctor.IsoAlgebra.overPowSuccFunctor c e n ⋙ Endofunctor.IsoAlgebra.stalk c τ x _ hx

variable (c) in
/-- The stalk at `x` of an algebra for `P e`, with its `(n + 1)`-st structure isomorphism. -/
noncomputable def Endofunctor.IsoAlgebra.frobeniusStalk {S : C} {s : S ⟶ S} (τ : P s ≅ 𝟭 (D S))
    {V : Over T}
    (e : V ≅ V) (n : ℕ) (x : S ⟶ V.left) (hx : x ≫ (e.pow (n + 1)).hom.left = s ≫ x)
    (G : Endofunctor.IsoAlgebra (P e.hom.left)) : Endofunctor.IsoAlgebra (𝟭 (D S)) :=
  (Endofunctor.IsoAlgebra.frobeniusStalkFunctor c τ e n x hx).obj G

variable (c) in
/-- The Frobenius stalk at `w` of the pullback of an algebra along `g`
(`Endofunctor.IsoAlgebra.overPullback`). -/
noncomputable def Endofunctor.IsoAlgebra.pullbackFrobeniusStalk {X W : Over T} (eX : X ≅ X) (eW : W
    ≅ W)
    {g : W ⟶ X} (hg : eW.hom ≫ g = g ≫ eX.hom) (n : ℕ) {S : C} {s : S ⟶ S} (τ : P s ≅ 𝟭 (D S))
    (w : S ⟶ W.left) (hw : w ≫ (eW.pow (n + 1)).hom.left = s ≫ w)
    (F : Endofunctor.IsoAlgebra (P eX.hom.left)) : Endofunctor.IsoAlgebra (𝟭 (D S)) :=
  (Endofunctor.IsoAlgebra.frobeniusStalkFunctor c τ eW n w hw).obj
      ((Endofunctor.IsoAlgebra.overPullback c eX eW hg).obj F)

/-- **Stalks of iterated pullbacks of algebras**: the composition isomorphism
`P w (P g F) ≅ P (w ≫ g) F` is an isomorphism between the stalk at `w` of the `(n + 1)`-st
iterate of the pullback of `F` along `g`, and the stalk at `w ≫ g` of the `(n + 1)`-st iterate
of `F`. -/
theorem Endofunctor.IsoAlgebra.nonempty_stalk_overPowSucc_overPullback_iso (hc : PullbackAssoc P c)
    {X W : Over T} (eX : X ≅ X) (eW : W ≅ W) {g : W ⟶ X} (hg : eW.hom ≫ g = g ≫ eX.hom)
    (F : Endofunctor.IsoAlgebra (P eX.hom.left)) (n : ℕ) {S : C} {s : S ⟶ S}
    (τ : P s ≅ 𝟭 (D S)) (w : S ⟶ W.left) (hw : w ≫ (eW.pow (n + 1)).hom.left = s ≫ w)
    {x : S ⟶ X.left} (hx : w ≫ g.left = x) (hwg : x ≫ (eX.pow (n + 1)).hom.left = s ≫ x) :
    Nonempty (Endofunctor.IsoAlgebra.pullbackFrobeniusStalk c eX eW hg n τ w hw F ≅
      Endofunctor.IsoAlgebra.frobeniusStalk c τ eX n x hwg F) := by
  subst hx
  have hgn := Iso.pow_hom_comp_eq_comp_pow_hom eW eX hg n
  refine ⟨Endofunctor.IsoAlgebra.isoMk ((c w g.left).app F.carrier).symm ?_⟩
  change (c w g.left).inv.app F.carrier ≫
      ((pullbackFamilyStalkComparison (c := c) τ (w ≫ g.left) _ hwg).hom.app F.carrier ≫
        (P (w ≫ g.left)).map
          (eX.powSuccStr (fun f ↦ P f.left) (fun f f' ↦ c f.left f'.left) F.str n).hom) =
    ((pullbackFamilyStalkComparison (c := c) τ w _ hw).hom.app ((P g.left).obj F.carrier) ≫
        (P w).map (eW.powSuccStr (fun f ↦ P f.left) (fun f f' ↦ c f.left f'.left)
          ((Endofunctor.IsoAlgebra.overPullback c eX eW hg).obj F).str n).hom) ≫
      (c w g.left).inv.app F.carrier
  exact pullbackFamilyStalkComparison_pullbackFamilyComparison' hc τ g.left _ _
    (Over.left_comp_left_eq_of_comp_eq hgn) _ _
    (Iso.powSuccStr_hom_eq_of_hom_eq (P := fun {X Y : Over T} (f : X ⟶ Y) ↦ P f.left)
      (c := fun {X Y Z : Over T} (f : X ⟶ Y) (g : Y ⟶ Z) ↦ c f.left g.left) hc.over eW eX g hg
      F.str ((Endofunctor.IsoAlgebra.overPullback c eX eW hg).obj F).str rfl n) w hw hwg

/-- `Endofunctor.IsoAlgebra.nonempty_stalk_overPowSucc_overPullback_iso` for functors given through
equations:
this form lets concrete instances use their own functors.

Implementation note: the categories are passed as variables, with their category instances, together
with `Sigma`-type equations to the generic ones, and the functors through `HEq` hypotheses. This
works around elaboration problems: instantiated directly with the pullbacks of module objects,
the generic statement makes the elaborator and the kernel unfold these pullbacks while comparing
the instances of the generic categories with the concrete ones. Concrete callers pass their own
categories and functors, together with `rfl` and functor-level equations. -/
theorem Endofunctor.IsoAlgebra.nonempty_obj_obj_iso_of_eq (hc : PullbackAssoc P c) {X W : Over T}
    (eX : X ≅ X) (eW : W ≅ W) {g : W ⟶ X} (hg : eW.hom ≫ g = g ≫ eX.hom)
    (n : ℕ) {S : C} {s : S ⟶ S}
    (τ : P s ≅ 𝟭 (D S)) (w : S ⟶ W.left) (hw : w ≫ (eW.pow (n + 1)).hom.left = s ≫ w)
    {x : S ⟶ X.left} (hx : w ≫ g.left = x) (hwg : x ≫ (eX.pow (n + 1)).hom.left = s ≫ x)
    (𝒜X 𝒜W ℬ : Type _) {i𝒜X : Category 𝒜X} {i𝒜W : Category 𝒜W} {iℬ : Category ℬ}
    (F : 𝒜X) (Λ₁ : 𝒜X ⥤ 𝒜W) (Φ : 𝒜W ⥤ ℬ) (Ψ : 𝒜X ⥤ ℬ)
    (h𝒜X : (⟨𝒜X, i𝒜X⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eX.hom.left), inferInstance⟩)
    (h𝒜W : (⟨𝒜W, i𝒜W⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eW.hom.left), inferInstance⟩)
    (hℬ : (⟨ℬ, iℬ⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (𝟭 (D S)), inferInstance⟩)
    (hΛ₁ : HEq Λ₁ (Endofunctor.IsoAlgebra.overPullback c eX eW hg))
    (hΦ : HEq Φ (Endofunctor.IsoAlgebra.frobeniusStalkFunctor c τ eW n w hw))
    (hΨ : HEq Ψ (Endofunctor.IsoAlgebra.frobeniusStalkFunctor c τ eX n x hwg)) :
    Nonempty (Φ.obj (Λ₁.obj F) ≅ Ψ.obj F) := by
  cases h𝒜X
  cases h𝒜W
  cases hℬ
  cases hΛ₁
  cases hΦ
  cases hΨ
  exact Endofunctor.IsoAlgebra.nonempty_stalk_overPowSucc_overPullback_iso hc eX eW hg F n τ w hw
      hx hwg


end Over

end CategoryTheory
