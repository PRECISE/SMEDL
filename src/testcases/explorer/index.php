<html>
<head>
    <link rel="stylesheet" type="text/css" href="web/style.css">
    <script src="http://code.jquery.com/jquery-1.11.2.min.js"></script>
    <script src="http://code.jquery.com/jquery-migrate-1.2.1.min.js"></script>
    <script src="http://jqueryrotate.googlecode.com/svn/trunk/jQueryRotate.js"></script>
    <script src="web/explorer.js"></script>
</head>
<body>
    <div id="map">
        <img src="web/img/roomba_small.png" id="explorer"/>
    </div>
    <div class="control">
        <form>
            <input id="info" type="button" value="Move!" onclick="moveOnRoute();" />
        </form>
        <div id="label"></div>
    </div>
</body>
</html>