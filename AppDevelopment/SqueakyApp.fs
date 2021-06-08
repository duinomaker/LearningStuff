namespace SqueakyApp

open Fabulous
open Fabulous.XamarinForms
open Xamarin.Forms
open System.Net
open System.Web
open System.Text
open System.Text.RegularExpressions

module ZF =

    type Client() =
        let mutable id = ""
        let mutable client = new WebClient()
        let mutable cookieContainer = CookieContainer()

        member this.UpdateCookies() =
            let cookies = client.ResponseHeaders.Get "Set-Cookie"

            if cookies <> null then
                cookieContainer.SetCookies(System.Uri "http://jwxt.njupt.edu.cn", cookies)

        member this.CookieString =
            System.Uri "http://jwxt.njupt.edu.cn/"
            |> cookieContainer.GetCookies
            |> fun l -> [ for c in l -> $"{c.Name}={c.Value}" ]
            |> List.reduce (fun a b -> $"{a}; {b}")

        member this.GetCodeImage callback =
            let bytes =
                System.Uri "http://jwxt.njupt.edu.cn/CheckCode.aspx"
                |> client.DownloadData

            this.UpdateCookies()
            callback bytes

        member this.Login id' password code =
            id <- id'
            let url = "http://jwxt.njupt.edu.cn/default2.aspx"

            let data =
                $"__VIEWSTATE=dDwxNTMxMDk5Mzc0Ozs%%2BRyHxH2kXFD%%2B/obehGIlm7rWAdYo=&txtUserName={id'}&Textbox1=&TextBox2={
                                                                                                                               password
                }&txtSecretCode={code}&RadioButtonList1=%%D1%%A7%%C9%%FA&Button1=&lbLanguage=&hidPdrs=&hidsc="
                |> Encoding.ASCII.GetBytes

            client.Headers.Set("Content-Type", "application/x-www-form-urlencoded")
            client.Headers.Set("Cookie", this.CookieString)

            let response =
                client.UploadData(System.Uri url, "POST", data)

            this.UpdateCookies()

            Encoding.RegisterProvider CodePagesEncodingProvider.Instance

            let html =
                (Encoding.GetEncoding "gb2312").GetString response

            match html.Contains "欢迎您" with
            | true -> Ok()
            | false -> Error()

        member this.GetClassroomPage() =
            let url =
                $"http://jwxt.njupt.edu.cn/xxjsjy.aspx?xh={id}&gnmkdm=N121611"

            let referer =
                $"http://jwxt.njupt.edu.cn/xs_main.aspx?xh={id}"

            client.Headers.Set("Content-Type", "application/x-www-form-urlencoded")
            client.Headers.Set("Cookie", this.CookieString)
            client.Headers.Add("Referer", referer)

            let response = client.DownloadData(System.Uri url)
            this.UpdateCookies()

            (Encoding.GetEncoding "gb2312").GetString response

        member this.GetEmptyClassrooms() =
            let url =
                $"http://jwxt.njupt.edu.cn/xxjsjy.aspx?xh={id}&gnmkdm=N121611"

            let html = this.GetClassroomPage()

            let viewstate =
                (Regex """name="__VIEWSTATE" value="([^"]+)""")
                    .Matches html
                |> fun mc -> [ for i in mc -> i ] |> List.last
                |> fun m -> [ for i in m.Groups -> i ] |> List.last
                |> fun g -> g.Value
                |> HttpUtility.UrlEncode

            let day, year =
                (Regex """selected="selected" value="([0-9]{3})">([0-9]{4})-[0-9]{2}-[0-9]{2}""")
                    .Matches html
                |> fun mc -> [ for i in mc -> i ] |> List.head
                |> fun m -> [ for i in m.Groups -> i ]
                |> fun gc -> [ for i in gc -> i.Value ]
                |> fun gl -> gl.[1], gl.[2]

            let years =
                $"{(System.Int32.Parse year) - 1}-{year}"

            let weekday = day.[0]

            let parity =
                if (System.Int32.Parse $"{weekday}") % 2 = 0 then
                    "%CB%AB"
                else
                    "%B5%A5"

            let interval =
                (Regex """selected="selected" value="('[0-9]+'\|'[0-9',]+)""")
                    .Matches html
                |> fun mc -> [ for i in mc -> i ] |> List.head
                |> fun m -> m.Groups.[1].Value
                |> HttpUtility.UrlEncode

            let term =
                Regex.Matches(html, """id="xq"[^s]+selected="selected" value="([0-9])">""", RegexOptions.Multiline)
                |> fun mc -> [ for i in mc -> i ] |> List.head
                |> fun m -> m.Groups.[1].Value

            let data =
                $"__EVENTTARGET=&__EVENTARGUMENT=&__VIEWSTATE={viewstate}&xiaoq=&jslb=&min_zws=0&max_zws=&kssj={day}&jssj={
                                                                                                                               day
                }&xqj={weekday}&ddlDsz={parity}&sjd={interval}&Button2=%%BF%%D5%%BD%%CC%%CA%%D2%%B2%%E9%%D1%%AF&xn={
                                                                                                                        years
                }&xq={term}&ddlSyXn={years}&ddlSyxq={term}"
                |> Encoding.ASCII.GetBytes

            client.Headers.Set("Content-Type", "application/x-www-form-urlencoded")
            client.Headers.Set("Cookie", this.CookieString)
            client.Headers.Add("Referer", url)

            let response =
                client.UploadData(System.Uri url, "POST", data)

            this.UpdateCookies()

            Encoding.RegisterProvider CodePagesEncodingProvider.Instance
            (Encoding.GetEncoding "gb2312").GetString response

        member this.GetEmptyClassroomList() =
            let html = this.GetEmptyClassrooms()

            (Regex """<td>((:?教[0-9]|教东|教西|无|锁金－).+?)</td>""")
                .Matches html
            |> fun mc -> [ for i in mc -> i ]
            |> List.map (fun m -> m.Groups.[1].Value)
            |> List.reduce (fun a b -> $"{a}\n{b}")

module App =

    type UserStat =
        | Waiting
        | LoggingIn
        | LoggedIn
        | AuthFailed

    type Model =
        { userStat: UserStat
          client: ZF.Client
          codeImage: byte []
          pageContent: string }

    type Msg =
        | RequestNewCodeImage
        | UpdateCodeImage of byte []
        | LoginClicked of string * string * string
        | LoginSuccess
        | AuthError
        | UpdatePageContent of string

    let newCodeImage (client: ZF.Client) =
        async {
            do! Async.SwitchToThreadPool()
            let mutable bytes = Array.empty
            client.GetCodeImage(fun bytes' -> bytes <- bytes')
            return UpdateCodeImage bytes
        }
        |> Cmd.ofAsyncMsg

    let authUser (client: ZF.Client) id password code =
        async {
            do! Async.SwitchToThreadPool()
            let result = client.Login id password code

            return
                match result with
                | Ok _ -> LoginSuccess
                | Error _ -> AuthError
        }
        |> Cmd.ofAsyncMsg

    let updatePageContent (client: ZF.Client) =
        async {
            do! Async.SwitchToThreadPool()
            let content = client.GetEmptyClassroomList()
            return UpdatePageContent content
        }
        |> Cmd.ofAsyncMsg

    let init () =
        let client = ZF.Client()

        { userStat = Waiting
          client = client
          codeImage = Array.empty
          pageContent = "" },
        newCodeImage client

    let update msg model =
        match msg with
        | RequestNewCodeImage -> { model with codeImage = Array.empty }, newCodeImage model.client
        | UpdateCodeImage bytes -> { model with codeImage = bytes }, Cmd.none
        | LoginClicked (id, password, code) ->
            { model with userStat = LoggingIn }, authUser model.client id password code
        | LoginSuccess ->
            { model with
                  userStat = LoggedIn
                  pageContent = "正在查询……" },
            updatePageContent model.client
        | AuthError ->
            { model with
                  userStat = AuthFailed
                  codeImage = Array.empty },
            newCodeImage model.client
        | UpdatePageContent content -> { model with pageContent = content }, Cmd.none

    let loginPage model dispatch =
        let loginForm =
            let mutable id = ""
            let mutable password = ""
            let mutable code = ""

            let idEntryCell =
                View.Entry(
                    maxLength = 32,
                    placeholder = "学号",
                    textChanged = fun textArgs -> id <- textArgs.NewTextValue
                )

            let passwordEntryCell =
                View.Entry(
                    isPassword = true,
                    maxLength = 20,
                    placeholder = "密码",
                    textChanged = fun textArgs -> password <- textArgs.NewTextValue
                )

            let codeEntryCell =
                View.Entry(
                    maxLength = 8,
                    placeholder = "验证码",
                    textChanged = fun textArgs -> code <- textArgs.NewTextValue
                )

            let codeImageCell =
                View.Button(
                    image = Image.Value.ImageBytes model.codeImage,
                    command =
                        fun () ->
                            if model.codeImage.Length <> 0 then
                                RequestNewCodeImage |> dispatch
                )

            let loginButton =
                View.Button(text = "登录", command = fun () -> LoginClicked(id, password, code) |> dispatch)

            [ idEntryCell
              passwordEntryCell
              codeEntryCell
              codeImageCell
              loginButton ]

        View.ContentPage(
            View.StackLayout(
                match model.userStat with
                | Waiting -> [ View.Label "请登录"; yield! loginForm ]
                | LoggingIn -> [ View.Label "正在登录……" ]
                | AuthFailed ->
                    [ View.Label "登录失败，请重试"
                      yield! loginForm ]
                | _ -> []
            )
        )

    let classroomPage model dispatch =
        View.ContentPage(View.StackLayout([ View.Label model.pageContent ]))

    let view model dispatch =
        let page =
            match model.userStat with
            | LoggedIn -> classroomPage
            | _ -> loginPage

        page model dispatch

type App() as app =
    inherit Application()

    let runner =
        Program.mkProgram App.init App.update App.view
        |> Program.withConsoleTrace
        |> XamarinFormsProgram.run app
