<html>
<head>
    <link rel="stylesheet" type="text/css" href="style.css">
    <script src="//code.jquery.com/jquery-1.11.2.min.js"></script>
    <script src="//code.jquery.com/jquery-migrate-1.2.1.min.js"></script>
    <script src="http://jqueryrotate.googlecode.com/svn/trunk/jQueryRotate.js"></script>
    <script src="explorer.js"></script>
</head>
<body>
    <div id="map">
        <img src="roomba_small.png" id="explorer"/>
    </div>
    <div class="control">
        <form>
            <input id="info" type="button" value="Move!" onclick="moveOnRoute();" />
        </form>
        <div id="label"></div>
    </div>
</body>
</html>