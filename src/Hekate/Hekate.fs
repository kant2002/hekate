module Hekate

(* Введение

   Библиотека для работы с графами в чисто функциональном виде, основываясь
   на идеях из статей об индуктивных графах и функциональных алгоритмах,
   в основаном от Мартина Эрвига. Эти статьи в особенности релевантны
   для понимания внутренностей этой библиотеки.

   Следующие статьи упоминаются в комментариях по всему коду:

   [Erwig:2001ho]: Индуктивные Графы и Функциональные Графовые Алгоритмы
                   http://dl.acm.org/citation.cfm?id=968434.968437

   Эта библиотека духовно схожа с Haskell библиотекой FGL, что
   не удивительно учитывая что она была изначально написана Эрвига и пр.,
   на основании [Erwig:2001ho]. Однако, мы упростили одни аспекты
   и изменили другие из-за собственных нужд и нужд системы типов.

   [FGL]: http://hackage.haskell.org/package/fgl

   There are some significant differences between Hekate and FGL:

   - Hekate does not have a concept of
     an unlabelled graph, either in terms of nodes or edges, and thus does
     not draw the FGL distinction between types Node, LNode, etc.

   - Hekate implements the underlying representation using a M type which
     is parameterized by key and value types, we allow node IDs to be of any
     type supporting comparison. Our graph type is this parameterized by the
     types of the node IDs, node labels, and edge labels.

   - Hekate does not draw a distinction between static and dynamic graphs.
     The Graph<_,_,_> type is always dynamic.

   NOTE: [Erwig:2001ho] defines various functions and algorithms implemented using
   the Basic Graph Operations. These are interesting, and usually the best way
   to understand the principle of the implementation, but they are not always the
   most efficient way to implement the function, depending on the underlying data
   structure representation. *)

open System
open Aether
open Aether.Operators

(* Прелюдия

   Useful utility functions used throughout Hekate. *)

let private flip f a b =
    f b a

let private обменять (a, b) =
    (b, a)

(* Определяющие Типы и Линзы

   Типы определяющие структуры данных которые формируют логическую
   модель программирования определяемая по индуктивному определению графов,
   совместно с набором линз для доступа к вложенным структурам данных. *)

type Вершина<'v> =
    'v

type Ребро<'v> =
    'v * 'v

type LNode<'v,'a> =
    'v * 'a

type LEdge<'v,'b> =
    'v * 'v * 'b

type Сосед<'v,'b> =
    ('b * 'v) list

type Контекст<'v,'a,'b> =
    Сосед<'v,'b> * 'v * 'a * Сосед<'v,'b>

let private пред_ : Lens<Контекст<'v,_,'b>, Сосед<'v,'b>> =
    (fun (п, _, _, _) -> п), (fun п (_, v, л, н) -> (п, v, л, н))

let private знач_ : Lens<Контекст<'v,_,_>, 'v> =
    (fun (_, з, _, _) -> з), (fun v (п, _, л, н) -> (п, v, л, н))

let private насл_ : Lens<Контекст<'v,_,'b>, Сосед<'v,'b>> =
    (fun (_, _, _, н) -> н), (fun н (п, в, л, _) -> (п, в, л, н))

(* Representational Types and Lenses

   Types used for the underlying implementation of the graph, modelling the
   logically defined inductive definition as an optimized map, with sub-maps
   defining node adjacencies. *)

type ОСосед<'v,'b> when 'v: comparison =
    Map<'v,'b>

type ОКонтекст<'v,'a,'b> when 'v: comparison =
    ОСосед<'v,'b> * 'a * ОСосед<'v,'b>

type ОГраф<'v,'a,'b> when 'v: comparison =
    Map<'v, ОКонтекст<'v,'a,'b>>

type Граф<'v,'a,'b> when 'v: comparison =
    ОГраф<'v,'a,'b>

let private опред_ : Lens<ОКонтекст<'v,_,'b>, ОСосед<'v,'b>> =
    (fun (п, _, _) -> п), (fun п (_, л, н) -> (п, л, н))

let private онасл_ : Lens<ОКонтекст<'v,_,'b>, ОСосед<'v,'b>> =
    (fun (_, _, н) -> н), (fun н (п, л, _) -> (п, л, н))

(* Отображения

   Функции отображения между двумя определяющими и репрезентатиными семействами структур данных,
   используются когда переводятся между алгоритмическими 
   операциями применяемыми к определяющей модели, и модификации used when translating between algorithmic operations applied
   to the definitional model, and modifications to the underlying data structure of
   the optmized representational model. *)

let private изСосед<'v,'b when 'v: comparison> : Сосед<'v,'b> -> ОСосед<'v,'b> =
    List.map обменять >> Map.ofList

let private вСосед<'v,'b when 'v: comparison> : ОСосед<'v,'b> -> Сосед<'v,'b> =
    Map.toList >> List.map обменять

let private изКонтекста<'v,'a,'b when 'v: comparison> : Контекст<'v,'a,'b> -> ОКонтекст<'v,'a,'b> =
    fun (п, _, l, н) -> изСосед п, l, изСосед н

let private вКонтекст<'v,'a,'b when 'v: comparison> v : ОКонтекст<'v,'a,'b> -> Контекст<'v,'a,'b> =
    fun (п, l, н) -> вСосед п, v, l, вСосед н

(* Construction

   The functions "Empty" and "&", forming the two basic construction
   functions for the inductive definition of a graph, as defined in the
   table of Basic Graph Operations in [Erwig:2001ho].

   "Empty" is defined as "empty", and "&" is defined as the function
   "compose". *)

type Ид<'v> =
    'v -> 'v

let private пустой : Граф<'v,'a,'b> =
    Map.empty

let private составитьГраф c v p s =
        Optic.set (Map.value_ v) (Some (изКонтекста c))
     >> flip (List.fold (fun g (b, v') -> (Map.add v b ^% (Map.key_ v' >?> онасл_)) g)) p
     >> flip (List.fold (fun g (b, v') -> (Map.add v b ^% (Map.key_ v' >?> опред_)) g)) s

let private составить (c: Контекст<'v,'a,'b>) : Ид<Граф<'v,'a,'b>> =
    составитьГраф c (c ^. знач_) (c ^. пред_) (c ^. насл_)

(* Декомпозиция

   Functions for decomposing an existent graph through a process
   of matching, as defined in the table of Basic Graph Operations
   in [Erqig:2001ho].

   The Empty-match function is named "isEmpty" and forms part of the public
   API for Hekate and is thus defined later in the Graph module. The "&-match"
   function becomes "decompose", and the "&v" function becomes "decomposeSpecific", to
   better align with F# expectations. *)

let private разложитьКонтекст v =
        Map.remove v ^% опред_
     >> Map.remove v ^% онасл_
     >> вКонтекст v

let private разложитьГраф v p s =
        Map.remove v
     >> flip (List.fold (fun g (_, a) -> (Map.remove v ^% (Map.key_ a >?> онасл_)) g)) p
     >> flip (List.fold (fun g (_, a) -> (Map.remove v ^% (Map.key_ a >?> опред_)) g)) s

let private разложитьКонкретный v (g: Граф<'v,'a,'b>) =
    match Map.tryFind v g with
    | Some mc ->
        let c = разложитьКонтекст v mc
        let g = разложитьГраф v (c ^. пред_) (c ^. насл_) g

        Some c, g
    | _ ->
        None, g

let private разложить (g: Граф<'v,'a,'b>) : Контекст<'v,'a,'b> option * Граф<'v,'a,'b> =
    match Map.tryFindKey (fun _ _ -> true) g with
    | Some v -> разложитьКонкретный v g
    | _ -> None, g

let private пуст<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> bool =
    Map.isEmpty

(* Функции

   Useful functions defined in terms of the Basic Graph Operations, though
   not expected to be used directly. *)

let rec private ufold f u =
       разложить
    >> function | Some c, g -> f c (ufold f u g)
                | _ -> u

let private свертка f xs : Граф<'v,'a,'b> -> Граф<'v,'a,'b> =
    flip (List.fold (flip f)) xs

(* Граф

   The "public" API to Hekate is exposed as the Граф[.[Edges|Узлы]] modules,
   providing an API stylistically similar to common F# modules like List, Map, etc.

   F# naming conventions have been applied where relevant, in contrast to
   either FGL or [Erwig:2001ho]. *)

[<RequireQualifiedAccess>]
module Граф =

    [<RequireQualifiedAccess>]
    module Ребра =

        (* Операции *)

        let добавить ((v1, v2, e): LEdge<'v,'b>) =
                Map.add v2 e ^% (Map.key_ v1 >?> онасл_)
             >> Map.add v1 e ^% (Map.key_ v2 >?> опред_)

        let добавитьНесколько es =
                свертка добавить es

        let убрать ((v1, v2): Ребро<'v>) =
                разложитьКонкретный v1
             >> function | Some (p, v, l, s), g -> составить (p, v, l, List.filter (fun (_, v') -> v' <> v2) s) g
                         | _, g -> g

        let убратьНесколько es =
                свертка убрать es

        (* Свойства *)

        let количество<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> int =
                Map.toArray
             >> Array.map (fun (_, (_, _, s)) -> (Map.toList >> List.length) s)
             >> Array.sum

        (* Отображение *)

        let отображение mapping : Граф<'v,'a,'b> -> Граф<'v,'a,'c> =
                Map.map (fun v (p, l, s) ->
                    Map.map (fun v' x -> mapping v' v x) p,
                    l,
                    Map.map (fun v' x -> mapping v v' x) s)

        (* Проекция *)

        let вСписок<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> LEdge<'v,'b> list =
                Map.toList
             >> List.map (fun (v, (_, _, s)) -> (Map.toList >> List.map (fun (v', b) -> v, v', b)) s)
             >> List.concat

        (* Запросы *)

        let содержит v1 v2 : Граф<'v,'a,'b> -> bool =
                Map.tryFind v1
             >> Option.bind (fun (_, _, s) -> Map.tryFind v2 s)
             >> Option.isSome


        let попробоватьНайти v1 v2 : Граф<'v,'a,'b> -> LEdge<'v,'b> option =
                Map.tryFind v1
             >> Option.bind (fun (_, _, s) -> Map.tryFind v2 s)
             >> Option.map (fun b -> (v1, v2, b))

        let найти v1 v2 =
                попробоватьНайти v1 v2
             >> function | Some e -> e
                         | _ -> failwith (sprintf "Edge %A %A Not Found" v1 v2)

    [<RequireQualifiedAccess>]
    module Вершины =

        (* Операции *)

        let добавить ((v, l): LNode<'v,'a>) =
                Map.add v (Map.empty, l, Map.empty)

        let добавитьНесколько ns =
                свертка добавить ns

        let убрать v =
                разложитьКонкретный v
             >> snd

        let убратьНесколько vs =
                свертка убрать vs

        (* Свойства *)

        let количество<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> int =
                Map.toArray
             >> Array.length

        (* Отображение *)

        let отображение mapping : Граф<'v,'a,'b> -> Граф<'v,'c,'b> =
                Map.map (fun v (p, l, s) ->
                    p, mapping v l, s)

        let отображениеСвертка mapping state : Граф<'v,'a,'b> -> 's * Граф<'v,'c,'b> =
                Map.toList
             >> List.mapFold (fun state (v, (p, l, s)) -> mapping state v l |> fun (c, state) -> (v, (p, c, s)), state) state
             >> fun (graph, state) -> state, Map.ofList graph

        (* Проекция *)

        let вСписок<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> LNode<'v,'a> list =
                Map.toList
             >> List.map (fun (v, (_, l, _)) -> v, l)

        (* Запросы *)

        let содержит v : Граф<'v,'a,'b> -> bool =
                Map.containsKey v

        let попробоватьНайти v : Граф<'v,'a,'b> -> LNode<'v,'a> option =
                Map.tryFind v
             >> Option.map (fun (_, l, _) -> v, l)

        let найти v =
                попробоватьНайти v
             >> function | Some n -> n
                         | _ -> failwith (sprintf "Node %A Not Found" v)

        (* Смежность и Степень *)

        let соседи в =
                Map.tryFind в
             >> Option.map (fun (p, _, s) -> Map.toList p @ Map.toList s)

        let наследники в =
                Map.tryFind в
             >> Option.map (fun (_, _, s) -> Map.toList s)

        let предшественники в =
                Map.tryFind в
             >> Option.map (fun (p, _, _) -> Map.toList p)

        let исходящие v =
                Map.tryFind v
             >> Option.map (fun (_, _, s) -> (Map.toList >> List.map (fun (v', b) -> v, v', b)) s)

        let входящие v =
                Map.tryFind v
             >> Option.map (fun (p, _, _) -> (Map.toList >> List.map (fun (v', b) -> v', v, b)) p)

        let степень v =
                Map.tryFind v
             >> Option.map (fun (p, _, s) -> (Map.toList >> List.length) p + (Map.toList >> List.length) s)

        let полустепеньИсхода v =
                Map.tryFind v
             >> Option.map (fun (_, _, s) -> (Map.toList >> List.length) s)

        let полустепеньЗахода v =
                Map.tryFind v
             >> Option.map (fun (p, _, _) -> (Map.toList >> List.length) p)

    (* Операции *)

    let создать ns es : Граф<'v,'a,'b> =
        (Вершины.добавитьНесколько ns >> Ребра.добавитьНесколько es) пустой

    let пустой =
        пустой

    (* Свойства *)

    let пуст<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> bool =
        пуст

    (* Отображение *)

    let отображение f : Граф<'v,'a,'b> -> Граф<'v,'c,'d> =
        Map.map (fun v mc -> (вКонтекст v >> f >> изКонтекста) mc)

    let рев<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> Граф<'v,'a,'b> =
        Map.map (fun _ (p, l, s) -> (s, l, p))

    (* Obsolete (Deprecated) Functions

       To be removed in the 4.0 release of Hekate after adequate
       transition time. *)

    (* Операции *)

    [<Obsolete ("Use Граф.Ребра.add instead.")>]
    let addEdge =
        Ребра.добавить

    [<Obsolete ("Use Граф.Ребра.addMany instead.")>]
    let addEdges =
        Ребра.добавитьНесколько

    [<Obsolete ("Use Граф.Вершины.add instead.")>]
    let addNode =
        Вершины.добавить

    [<Obsolete ("Use Граф.Вершины.addMany instead.")>]
    let addNodes =
        Вершины.добавитьНесколько

    [<Obsolete ("Use Граф.Ребра.remove instead.")>]
    let removeEdge =
        Ребра.убрать

    [<Obsolete ("Use Граф.Ребра.removeMany instead.")>]
    let removeEdges =
        Ребра.убратьНесколько

    [<Obsolete ("Use Граф.Вершины.remove instead.")>]
    let removeNode =
        Вершины.убрать

    [<Obsolete ("Use Граф.Вершины.removeMany instead.")>]
    let removeNodes =
        Вершины.убратьНесколько

    (* Properties *)

    [<Obsolete ("Use Граф.Ребра.count instead.")>]
    let countEdges<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> int =
        Ребра.количество

    [<Obsolete ("Use Граф.Вершины.количество instead.")>]
    let countNodes<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> int =
        Вершины.количество

    (* Map *)

    [<Obsolete ("Use Граф.Ребра.map instead.")>]
    let mapEdges =
        Ребра.отображение

    [<Obsolete ("Use Граф.Вершины.map instead.")>]
    let mapNodes =
        Вершины.отображение

    (* Projection *)

    [<Obsolete ("Use Граф.Ребра.toList instead.")>]
    let edges<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> LEdge<'v,'b> list =
        Ребра.вСписок

    [<Obsolete ("Use Граф.Вершины.toList instead.")>]
    let nodes<'v,'a,'b when 'v: comparison> : Граф<'v,'a,'b> -> LNode<'v,'a> list =
        Вершины.вСписок

    (* Query *)

    [<Obsolete ("Use Граф.Ребра.contains instead.")>]
    let containsEdge =
        Ребра.содержит

    [<Obsolete ("Use Граф.Вершины.contains instead.")>]
    let containsNode =
        Вершины.содержит

    [<Obsolete ("Use Граф.Ребра.find instead.")>]
    let findEdge =
        Ребра.найти

    [<Obsolete ("Use Граф.Вершины.find instead.")>]
    let findNode =
        Вершины.найти

    [<Obsolete ("Use Граф.Ребра.tryFind instead.")>]
    let tryFindEdge =
        Ребра.попробоватьНайти

    [<Obsolete ("Use Граф.Вершины.tryFind instead.")>]
    let tryFindNode =
        Вершины.попробоватьНайти

    (* Adjacency and Degree *)

    [<Obsolete ("Use Граф.Вершины.neighbours instead.")>]
    let neighbours =
        Вершины.соседи

    [<Obsolete ("Use Граф.Вершины.successors instead.")>]
    let successors =
        Вершины.наследники

    [<Obsolete ("Use Граф.Вершины.predecessors instead.")>]
    let predecessors =
        Вершины.предшественники

    [<Obsolete ("Use Граф.Вершины.outward instead.")>]
    let outward =
        Вершины.исходящие

    [<Obsolete ("Use Граф.Вершины.inward instead.")>]
    let inward =
        Вершины.входящие

    [<Obsolete ("Use Граф.Вершины.степень instead.")>]
    let degree =
        Вершины.степень

    [<Obsolete ("Use Граф.Вершины.полустепеньИсхода instead.")>]
    let полустепеньИсхода =
        Вершины.полустепеньИсхода

    [<Obsolete ("Use Граф.Вершины.полустепеньЗахода instead.")>]
    let inwardDegree =
        Вершины.полустепеньЗахода
