# A könnyűzene formális modellje

## Abstract
A zenei jelfeldolgozással foglalkozó algoritmusok gyakran figyelmen kívül hagyják magának a zenének az elméletét. Ennek oka a formális zenei modell hiánya. A munkámban megmutatom, hogy a formalizált zeneelmélet felhasználható a jelfeldolgozási kimenetek gépi elbírálásában. Megvizsgálom, hogy a zenei modell megválasztása hogyan befolyásolja a feldolgozás egyes szintjeit, hogyan lehet segítségükre, és hogyan verifikálhatóak számítógéppel az eredményeik. Arra is kitérek, hogy ez a számítási zenetudományi feladat milyen szoftvertechnológiai kihívásokkal jár, és azok hogyan oldhatóak meg.  






## A kutatási célok meghatározása

A kutatás legfőbb célja megállapítani, hogy milyen eszközökkel lehetséges a zene modelljét formalizálni oly módon, hogy a kész modell könnyen beágyazható legyen zenei jelfeldolgozási feladatokba. Ennek hasznossága illetve szükségessége több szinten megnyilvánul valós projektekben.

[zenei modell szintjei kép: 1. követelmények, dokumentációk 2. reprezentálás 3. zeneelméleti definíciók, függvények 4. zenei kiértékelés]

 A zenei modell hiánya legalacsonyabb szinten a feladat megfoglamazásánál, a követelmények egyértelmű definiálásánál jelentkezik. A zenei projektekre jellemző, hogy mivel leggyakrabban zenei háttértudással rendelkező fejlesztők készítik azokat, a zenészek által ismert zeneelmélet mentén fogalmaznak, ezek  viszont gyakran pontatlanok tudnak lenni a különböző zenei stílusok különböző fogalmazásai miatt. John Rahn is ebből indul ki a *Logic, Set Theory, Music Theory* című kutatásában, melyben így fogalmaz: "The music-theoretical literature is a porridge of definitions fallen prey to various dangers, and worse, of "definitions" so-called which are utterances of every possible sort except the sort of definition. If only authors who cannot define would confine themselves to the "you know what I mean" mode of discourse, all would be well. But a statement falsely purporting to define, if taken seriously, utterly destroys the fabric of its context.". Fontos hozzátenni, hogy a művészet központú zeneelmélet nem tekinti céljának a formalizáltságot, ezért alátámasztható, hogy miért hoz meg döntéseket több esetben akár hagyomány alapján is. Ha a zeneelmélet ezen alapvető hiányosságától el is tekintünk, akkor is nehezen található olyan zeneelméleti összefoglaló, ami a hanghullámoktól a zenei formáig és stílusokig egybefüggően tárgyalja a témát, így tehát általánosságban rossz gyakorlat a művészeti zeneelmélet használata követelmények megfogalmazásánál.

[Kép béna zenei dokumentációról]
[Példa ellentmondó zeneelmélet könyvekből (konszonancia)]

A modell szerepe a zenei adatok tárolásában is megjelenik. Dalok reprezentálására két módszert használnak a gyakorlatban. Az egyik a hangok MIDI fájlként való tárolása. Ennek egyértelmű hátránya, hogy a ritmikai információ kinyerése feldolgozást igényel. Ennek oka, hogy a hangok kezdete és vége van csak eltárolva, a hangérték megállíptása pedig sok esetben nem egyértelmű ezek alapján. Minden hanghoz a hang magasságán kívűl még a hang erősségének értéke van feljegyezve. Ennek a számnak az interpretálása szintén nem egyértelmű, hiszen egyszerre fejezi ki a hangszer hangerejét, a hang dinamikáját, a dal adott részének a dinamikáját illetve akár a hang ütemben kapott szerepét is. Ezen indokok miatt a MIDI formátum bár a zene fizikai leírásának megfelelő reprezentáció tud lenni, sok esetben további feldolgozást igényel, így általánosságban véve nem tekinthető magasszintű zenei jelfeldolgozási feladatoknál megfelelő kimeneti formátumnak.

[MIDI példa, esetleg valami nem egyértelmű ritmikai dologról]

A zeneművek másik reprezentálási formája jellemzően valamilyen kottaszerű ábrázolást jelent. Bár ezen a területen megvalósítás és célkitűzések szempontjából széles skálán mozognak az eszközök, gyakori probléma viszont a jelfeldolgozáshoz való használatukban, hogy nem magát a zenét, hanem a kottát reprezentálják, ez pedig azon felül, hogy szükségtelen komplikációkat okoz, több esetben félrevezeti a fejlesztőket az eredmények értékelésénél, vagy a célok meghatározásában. Erre példaként hozható az ütemmutató és az ütemen belüli hangsúlyozás feljegyzése. Mivel az ütemmutató meghatározza, hogy az adott ütemen belül mely hangokra kerül nagyobb hangsúly, ezeken a hangokon kottában a megfelelő hangsúlyozást külön jelölni felesleges, viszont jelfeldolgozási feladatoknál minden egyes hang pontos hangsúlyozását elhagyni nagymértékű adatkiesést jelentene és nagyban megnehezítené a további feldolgozást. Ezen kívűl a kottába feljegyezhető dinamikai kifejezések gépi értelmezése lehetetlen vállalkozás lenne, ezek nélkül viszont nem megfelelő a zene reprezentálása kottában, így a kotta bár megfelelő végkimeneti formátum magasszintű jelfeldolgozási feladatoknak, a feladat végrehajtása közben viszont rossz gyakorlat a használata. Fontos megjegyezni, hogy léteznek olyan kottaszerű reprezentáló eszközök, amelyek jól kezelnek a most említett nehézségek közül többet is.

[Kotta példa]
[Music21 nem is olyan rossz példa]
[reprezentálás szintjei: alul MIDI felül kotta középen hiányzik a megfelelő eszköz]

Egy általános zenei modellre a jelfeldolgozás során mint függvény gyűjteményre is szükség van. Erre a problémára számos zeneelmélet könyvtár létezik, viszont ezek saját típusokat használnak, amik nehezen kapcsolódnak zenei reprezentációs eszközökhöz. Másik általános hiányosságuk, hogy a fizikai zeneelmélet definícióit nem tartalmazzák.

[Music21 voicing dolog hogy viszonyul egy többszólamú rész reprezentálásához MIDI-ben?]

Legmagasabb szinten pedig a zene formális modellje használható lenne jelfeldolgozó algoritmusok kimenetének zenei kiértékelésére. Bár ez használat szempontjából nem különül el a korábban említett zeneelmélet könyvtár eszközöktől, abból a szempontból fontos elkülöníteni mégis, hogy ez a feladat sokkal magasabb szintű zenei formalizálást igényel. Példaként hozható egy dal részeinek megnevezése, vagy műfajának felismerése.

[Ide is valami]


A modell formalizálásnak eszközének megválasztásán kívül megvizsgálom, azt is, hogy melyek azok a zeneelméleti területek illetve konkrét feladatok amelyeket egy ilyen modellnek tárgyalnia kell annak érdekében, hogy mai jelfeldolgozási feladatokat megfelelően tudjon támogatni. Az elmúlt évtizedekben a számítási zenetudomány leginkább klasszikus zene köré épített elemzéseket, melyek sokszor könnyűzenére nem értelmezhetőek, illetve az könnyűzenére átültethető analízisek közül is kevés olyan akad, aminek gyakorlati haszna lenne egy tipikus mai projektben. Az elmúlt években robbanásszerűen növekedett a zenei jelfeldolgozás alkalmazása. Megjelent a streaming szolgáltatóknál és a zenei megosztó felületeken is, megbízható működésüknek szükségét pedig mi sem fejezné ki jobban, mint hogy eredményeik gyakran jogi következményeket vonnak maguk után. A futurisztikusnak tűnő okoserősítőkben pedig nem ritka funkció már a virtuális zenekar, amely minden instrukció nélkül real time kíséri a játékost a dalban, vagy akár együtt improvizál vele. Egy ilyen eszköz korábban nem látott feladatok merülnek fel. 

Vizsgálni fogom a zenei analízis alapvető kérdését, a zene és nem zene elválasztását. Minél szigorúbb állításokkal fogom szűkíteni a könnyűzene fogalmát és tanulmányozni fogom ennek a szigorításnak a jelentősségét. Kitérek az ütem és az ehhez tartozó fogalmak jelentésére, különböző definiálási lehetőségeire és az ezekhez tartozó ütemmutató felismerésének lehetséges megvalósításaira. Végül pedig megvizsgálom, hogy milyen fogalmak mentén definiálható a zenei variáció és a variáció mentén hogyan adható meg egy dal felépítése és részeinek kapcsolata.

 - Szakdogám akkordelnevezője is azért olyan szuper, mert sokat tud a program a zenéről
 - zeneelmélet formális alapjait lerakni



## A problémakör irodalmának, az előzményének rövid áttekintése

A számítási zenetudomány területén írt kutatásokról elmondható, hogy leggyarkabban egy újfajta zenei analízist mutatnak be, vagy egy már megírt részleteit taglalják. Az elmúlt közel hatvan évben számos olyan analízis illetve ezekhez tartozó feladat akadt, melynek nagy jelentőséget nyilvánított a szakma. Ebben a fejezetben ezek közűl a legelterjedtebb négyet fogom bemutatni röviden és vizsgálni a relevanciáját a könnyűzene formális modelljének jelfeldolgozási feladatokban betöltött szerepének szempontjából, illetve körüljárom, hogy megvalósításuk hogyan lenne lehetséges.

### Schenkeri zeneelmélet, generatív grammatika és halmazelmélet

Heinrich Schenker zeneelmélete számos zenei analízis alapjává vált, mivel ez volt az első olyan formálisnak ható rendszer, amellyel meghatározható egy zene felépítése a formától egészen a dallam szintjéig. Lényege abban rejlik, hogy szabályok mentén az eredeti zenét abstract zenei felépítéssé egyszerűsíti, így adva magyarázatot egy adott zenei résznek. Ezek az absztrakt zenei felépítések, hiszen továbbra is zenéről beszélünk, tovább egyszerűsíthetőek. A legmagasabb szintű absztrakt kivonat, az úgynevezett alapvető struktúra (Ursatz) nagyjából megegyezik minden egyes tonális műnél, így ez az elmélet alkalmas arra, hogy megmutassa egy adott zenemű egyedisége milyen szinten lép fel, illetve jól rávilágít két mű közötti különbség szintjére is.

[Schenkeri példa]

Mivel Schenker zeneelmélete átírási szabályokon alapul, nagyon jól kapcsolatba hozható Chomsky transformációs generatív grammatikájával. Ezen az ötleten alapul Stephen W. Smoliar *A Computational Aid for Schenkerian Analysis* című cikkje, melyben az említett zenei analízist elvégző program működését részletezi. Ennek megvalósítása során Smoliar felismerte, hogy a Schenkeri zeneelmélet alapvető problémája az aluldefiniáltásg, így az csak alapgondolatok ötleteként szolgált a saját zeneelméletének formalizálásában.

[Példa a generatív grammatika és a schenkeri analízis hasonlatára]
[Példa a Smoliar cikkből]

Smoliar mellett John Rahn is kutatásában próbát tesz egy formális, de a Schenkeri zeneelmélethez hasonló modell felépítésére. A *Logic, Set Theory, Music Theory* című cikkében egy kezdetleges modellt épít fel halmazelmélettel, viszont a sorravett definíciókban hamar megjelennek korábban nem definiált zenei kifejezések, melyeket később sem tárgyal.

[IVA IVC mi az, hogy oktáv? hogy lehet IVC nélkül definiálni?]
[Nem tudom, belerakjam-e, de a whole tone skála nem cyclic ordering]

A kutatás arra is kitér, hogy a modell több szintaktikailag helyes, de elkerülendő, "ronda" zenei értelmezést is tud generálni. Ugyanígy "ronda" zeneművek is generálhatóak a modellből, vagy máshogy fogalmazva "nem zenék" is értelmezhetőek vele. Rahn szerint hiábavaló próbálkozás olyan elmélet megalkotásán dolgozni, amivel csak szép zenék és a legszebb elemzések állíthatóak elő.


### A tonális zene generatív elmélete (GTTM)

Fred Lerdhal és Ray Jackendoff 1977-es *Toward a Formal Theory of Tonal Music* kutatása új gondolatokat hozott a zene formalizálásának területére. Kitűzték, hogy a zeneelméletnek legalább négy doménje van, névlegesen csoportosító analízis, metrikus analízis, időintervallum redukció, és prolongációs redukció. Ezt a négyest a tonális zene generatív elméletének nevezték el. A modelljükben mind a négy elemzéshez a lehetséges struktúrális leírások meghatározására **well-formedness** szabályokat, a lehetséges leírások közötti a "tapasztalt hallgatónak" megfelelő leírás kiválasztására pedig **preference** szabályokat definiáltak. A csoportosító analízis a zenebén szereplő hangcsoportok hierarchiai rendjét adja meg, a metrikus analízis pedig az erős és gyenge ütések rendjét. A prolongációs redukció erősen párhuzamba hozható a Schenkeri zeneelmélettel, céljában megegyezik vele, míg a szabályokat a formalizáltság érdekében ahogy Smoliarnál és Rahnnál is láthattuk, máshogy kényszerűl definiálni. Az időintervallum redukció abban tér el a prolongációs redukciótól, hogy az egyszerűsítést a zene hangcsoportjain értelmezi.

[példa legalább egy analízisre szabályokkal]


### Összegzés a könnyűzene és a jelfeldolgozás szemszögéből 

Az említett cikkek jól szemléltetik a tudományág kutatásainak fókuszát. Bármely cikk, amely egy elméletet tárgyal, a tonális klasszikus zenét teszi az analízis mindenkori bemenetévé, bár egyértelmű, hogy sokkal nagyobb számban van szükség könnyűzene elemzésére. Ezt tekintve fontos a kérdés tehát, értelmezhetőek-e a klasszikuszene analítikai módszerei könnyűzenén? Mielőtt ezt a kérdést tovább bontanám, fontos megemlíteni a zenetudósok között egy nagyon elterjedt nézetet, az elemzési partikularizmust. **ide kell hivatkozás** A partikularista zenetudósok nem nyilvánítanak nagy jelentőséget az univerzális zenei elemzéseknek, mert úgy gondolják hogy a zeneművek egyediségéből következik, hogy analítikai eszközeiket is egyedileg kell megválasztani. A korábbi kérdés helyett tehát jobb feltenni azt, hogy milyen a könnyűzenére általánosan megállapítható tulajdonság kinyerésére lehet szükség a jelfeldolgozási feladatok során. A korábban bemutatott analíziseknél megfigyelhető, hogy nem fektetnek hangsúlyt az analízis céljának meghatározására, vagyis arra, hogy milyen információ kinyerésének a feladatát valósítja meg, hanem elsősorban lépéseit vázolják. Éppen ezért csak a saját analízisünk célkitűzései után lehet megvizsgálni, hogy a korábbi zeneelméletek közül felhasználható-e valamelyik a feladatra, ezt pedig egy formális rendszerben igazolni is tudnánk. *Értelmezhetőek-e akkor a klasszikuszene analítikai módszerei a könnyűzenén?* Sajnos a válasz az, hogy nem tudjuk, egyáltalán célrevezető-e értelmezni őket, bár valószínűleg értelmezhetőek, azonban azt sem tudhatjuk biztosan, hogy az eredmény mit fog jelenteni.

Ugyanennyire fontos, de egyszerűbb kérdés a következő: hogyan használhatóak fel ezek az analízisek zenei jeleken? Természetesen nem egy hatalmas lépésben szeretnénk kinyerni az információt a hanghullámból. A tipikus részfeladatok közé tartozik a különböző transzformációkkal a zenei adat, vagyis a zenei hangok kinyerése. A feladat ezen szintjén amikor zenei hangról beszélünk, igazán egy frekvenciára, egy kezdeti és befejezési időpontra, és különböző dinamikai jellemzőkre gondolunk. Ezeket a primitív zenei hangokat megfelelően tudjuk például MIDI-ben ábrázolni. Ahogy láthattuk az említett cikkek, ber erre külön nem térnek ki, de kottán definiálják az elemzéseket. Ez a gyakorlat elfogadható, lévén céljuk kész zeneművek leirat alapján történő elemzése. Ahhoz azonban, hogy ezeket felhasználhassuk jelfeldolgozás során is, a primitív zenei hangokat valahogyan kottába kell szednünk, vagy definiálnunk alacsonyabb szintre az eredeti analízisekkel megegyező analíziseket. Akárhogy is, a kotta és a nem kotta között tátongó lyukat, névlegesen az ütemmutatót, ritmust, hangnemet és hangneveket valahogyan át kell hidalni.

[hanghullám != primitív hang != kotta]


legyen olyan a modell, hogy több mindent megállapít

metrikai analízis kottán van elvégezve, de az lejegyzés, nem pedig maga a zene music gamma stb

 - nem foglalkoznak a zene struktúrák reprezentálásával
 - a mirnél felmerülő problémák nem pont ezek
 - dolgok összevissza vannak, nincs kipróbálható algoritmus és eszköz sem


konszonancia https://www.jstor.org/stable/40285261?seq=1
http://gttm.jp/hamanaka/wp-content/uploads/2015/12/ISMIR2007Tutorial_Slide.pdf
https://www.jstor.org/stable/900759

 - nagyon hiányos más szempontokból, pl funkcionális elemzés
 
 - S W Smoliar A Computer Aid for Schenkerian Analysisban is hasonlóan a Schenkeri zeneelméletet ülteti át Chomsky transformational generative grammatikájára
 - leírja a zenei hang ábrázolását a harmadik oldalon



## A téma feldolgozás során alkalmazott módszerek

### Az eszköz megválasztásáról
 - Coq, Agda
 - Mivel másabb, mint mondjuk egy python package

### Definíciók
 - Benson Mates' Elementary Logic (197-203): A definíció eliminable és non-creative kell, hogy legyen
 - John Rahn Logic, Set ... : A formalizálásnak épp úgy vonzó az esztétikus döntés, mint a praktikus.






## A téma feldolgozásának részletezése, részletes ismertetése

 - a modell szintjein végigmenni
 - követelményeknél nem lehet egy az egybe a coqot használni, de coqban le lehet írni állításokatt a zenei kifejezésekre, ezekre lehet hivatkozni a követelményekben.

### A zenei hang formalizálásáról

 - S W Smoliar A Computer Aid for Schenkerian Analysisban is hasonlóan a Schenkeri zeneelméletet ülteti át Chomsky transformational generative grammatikájára
 - leírja a zenei hang ábrázolását a harmadik oldalon

 - A zenei hang szintjei
 - Más eszközök hogyan formalizálják
 - szintaktikai cukrok
 - állítások, bizonyítások
 - példa, hogy máshol ezt rosszul csinálták (az én modellem szerint)

### A ritmus formalizálásáról
 - division és duration formalizálása (nem túl izgalmas)
 - az ütemmutató nem része a zenének, de megállapítható róla
 - példa: egy ütemmutató algoritmus kiértékel egy hangfájlt, én pedig a modellemmel a hangfájl leiratának birtokában megmondom, hogy jó-e. Végülis egy bizonyítás, de igazán csak egy unit teszt.

### A zenei struktúra formalizálásáról
 - dallam
 - többszólamú zene lehetséges formalizálásai
 - variáció definiálása
 - a zene részeinek elkülönítése
 
### A modell beágyazása projektekbe
 - példa paraméterezhető automatikus bizonyításra, amit egy másik program használni tud
 - a modellt lehet végülis szintetizálásra használni, így könnyen előállíthatók algoritmusoknak teszt esetek, amiket könnyű vizsgálni









## Az eredmények összefoglaló értékelése és a levonható következtetések

 - mit lehetett bebizonyítani a zenei struktúrákra
 - mindent kapcsolatba hoz az eszköz mindennel: Midit a kottával, művészi zeneelméletet a fizikával, zenetudományi kutatásokat jelfeldolgozási projektekkel
 - Toward a formal theory 2. oldal "One of the virtues of formal theory ..."




## Belefoglalni
 - megírom coq a zeneelméletet   
 - veszek egy algoritmust ami állít valamit valamilyen zenéről, ezt agdával bebizonyítom   
 - tehát vannak különbözőek. Például egy másik modell lenne, ha zenei hangok csak számok lennének.   
 - frekvencia szinten mik állapíthatóek meg, hang szinten, teljes egészében véve   
 - tehát mutatok arra példát, hogy valahogy visszacsatolni a részeredményt, hogy finomuljon az algoritmus   
 - tudok-e valami olyat írni, ami automatikusan bizonyít egy parametizálható állítást (pl. ez a dallam F dúrból C-be majd vissza F-be vált)   
 - Lehet-e ezt végül coq csinálni? Lassú lesz? hogyan integrálom? Esetleg megírom pythonban is és összehasonlítom.   
 - Keresek valami zenei algoritmust, amit be tudok bizonyítani, hogy hibásan működik


## gondolkozok

variáció eszközei:
 - transzponálás
 - elnyújtás
 - díszítás
 - egyszerűsítés
 - harmónia helyettesítés 
 - Refrént már azelőtt érezzük, hogy elkezdődne  
 - A és B elkülönítése több lépésben. Addig csökken a lehetséges különbség értéke, amíg fel nem ismerődik a két különböző rész.
 
 
 
 1 alkalmazott módszerek
 2 feldolgozás részletezése
 3 -||-
 4 eredmények
 5 képek
 6
 7

