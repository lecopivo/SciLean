import SciLean.Data.DataArray.DataArray

namespace SciLean.DataArrayN

@[pp_dot]
abbrev mapMono [IndexType I] [PlainDataType X]
    (x : DataArrayN X I) (f : X → X) :=
  ArrayType.mapMono f x

@[pp_dot]
abbrev mapIdxMono [IndexType I] [PlainDataType X]
    (x : DataArrayN X I) (f : I → X → X) :=
  ArrayType.mapIdxMono f x

@[pp_dot]
abbrev fold [IndexType I] [PlainDataType X]
    (x : DataArrayN X I) (f : Y → X → Y) (init : Y):=
  LeanColls.Fold.fold x f init

@[pp_dot]
abbrev foldIdx [IndexType I] [PlainDataType X]
    (x : DataArrayN X I) (f : I → Y → X → Y) (init : Y) :=
  LeanColls.Fold.fold (LeanColls.Indexed.WithIdx.mk x) (fun y (i,x) => f i y x) init

@[pp_dot]
abbrev reduceD [IndexType I] [PlainDataType X]
    (x : DataArrayN X I) (f : X → X → X) (default : X):=
  IndexType.reduceD (fun i => x[i]) f default

@[pp_dot]
abbrev reduce [IndexType I] [PlainDataType X] [Inhabited X]
    (x : DataArrayN X I) (f : X → X → X) :=
  IndexType.reduce (fun i => x[i]) f


@[pp_dot]
abbrev max [IndexType I] [PlainDataType X] [Max X] [Inhabited X]
    (x : DataArrayN X I) : X :=
  IndexType.reduce (fun i : I => x[i]) (Max.max · ·)

@[pp_dot]
abbrev min [IndexType I] [PlainDataType X] [Min X] [Inhabited X]
    (x : DataArrayN X I) : X :=
  IndexType.reduce (fun i : I => x[i]) (Min.min · ·)
