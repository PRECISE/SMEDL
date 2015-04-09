var orientation = 0;
var coordinates = {x:0, y:0};
var drive_angles = [];
var targets = [];
var obstacles = [];
var failed = false;

$(document).ready(function() {
    //initExplorer(1,0,-45);
    randomInitExplorer();
    addTargets(20);
    addObstacles(50);
    makeTextMap();
    // $("#label").text(mapToString(false));
    $("#label").text(getRoute());
});

function randomInitExplorer() {
    y = Math.floor(Math.random() * 10);
    x = Math.floor(Math.random() * 20);
    angle = Math.floor(Math.random() * 8) * 45;
    initExplorer(y, x, angle);
}

function initExplorer(y, x, angle) {
    coordinates.y = y;
    coordinates.x = x;
    var explorer = document.getElementById("explorer");
    explorer.style.top = (y * 50) + "px";
    explorer.style.left = (x * 50) + "px";
    $("#explorer").rotate(angle);
    orientation = angle;
    drive_angles.push(angle);
}

function moveOnRoute() {
    var input = parseRouteString(getRoute());
    calculateDriveAngles(input);
    var move_times = calculateMoveTimes(drive_angles);
    for (i = 0; i < input.length; i++) {
        (function(index) {
            setTimeout(function() { moveOnGrid(input[index], index); }, move_times[index]);
        })(i);
    }
}

function getRoute() {
    var xmlHttp = new XMLHttpRequest();
    var params_string = mapToString(false);
    xmlHttp.open( "GET", "web/control.php?coordinates=" + params_string, false );
    xmlHttp.send( null );
    return xmlHttp.responseText;
}

function parseRouteString(str) {
    var pairs = str.split(" ");
    return pairs.map( function(pair) { return pair.split(","); } );
}

function calculateDriveAngles(input) {
    for(i = 0; i < input.length; i++) {
        var y_change = input[i][0];
        var x_change = input[i][1];
        if(x_change == 0 && y_change > 0) {
            angle = 90;
        } else if(x_change == 0 && y_change < 0) {
            angle = 270;
        } else if(x_change > 0 && y_change >= 0) {
            angle = Math.atan(y_change/x_change) * 180 / Math.PI;
        } else if(x_change > 0 && y_change < 0) {
            angle = 360 + Math.atan(y_change/x_change) * 180 / Math.PI;
        } else if(x_change < 0 && y_change >= 0) {
            angle = 180 + Math.atan(y_change/x_change) * 180 / Math.PI;;
        } else if(x_change < 0 && y_change < 0) {
            angle = 180 + Math.atan(y_change/x_change) * 180 / Math.PI;;
        }
        drive_angles.push(angle);
    }
}

function calculateMoveTimes(angles) {
    var move_times = [0];
    for (i = 1; i < drive_angles.length; i++) {
        rotation_time = calculateRotationTime(i);
        running_total = move_times[i - 1];
        move_times.push(running_total + rotation_time + 600); //time 2000
    }
    return move_times;
}

function calculateRotationTime(end_index) {
    if(end_index == 0) {
        return 0;
    }
    var difference = Math.abs(calculateDegreeDifference(end_index));
    if(difference > 180) {
        difference = 360 - difference;
    }
    return difference * 10; //time 20
}

function calculateDegreeDifference(end_index) {
    start_angle = drive_angles[end_index - 1];
    end_angle = drive_angles[end_index];
    return end_angle - start_angle;
}

function moveOnGrid(loc_change, index) {
    checkForItems();
    if(failed) {
        return;
    }
    var y = 50 * loc_change[0];
    var x = 50 * loc_change[1];
    var left_direction = "+=" + x;
    var top_direction = "+=" + y;
    var end_angle = drive_angles[index + 1];
    if(calculateDegreeDifference(index + 1) > 180) {
        end_angle = end_angle - 360;
    } else if (calculateDegreeDifference(index + 1) < -180) {
        end_angle = end_angle + 360;
    }
    $("#explorer").rotate({
        duration: calculateRotationTime(index + 1),
        angle: drive_angles[index],
        animateTo: end_angle,
        easing: $.easing.easeInOutElastic
    });
    window.setTimeout(function(){moveExplorer(left_direction, top_direction);}, calculateRotationTime(index + 1)); //time 800
    coordinates.y = coordinates.y + parseInt(loc_change[0]);
    coordinates.x = coordinates.x + parseInt(loc_change[1]);
}

function moveExplorer(left_direction, top_direction) {
    $("#explorer").animate({left: left_direction, top: top_direction}, 600);   //time 1600
}

function checkForItems() {
    for(i = 0; i < targets.length; i ++) {
        if(targets[i][0] == coordinates.y && targets[i][1] == coordinates.x) {
            var img = document.getElementById("img" + targets[i][0] + targets[i][1]);
            img.style.display = "none";
            targets.splice(i, 1);
        }
    }
    for(i = 0; i < obstacles.length; i ++) {
        if(obstacles[i][0] == coordinates.y && obstacles[i][1] == coordinates.x) {
            var img = document.getElementById("explorer");
            img.src = "img/explosion.png";
            failed = true;
        }
    }
}

function addTargets(quantity) {
    generateTargetCoordinates(quantity);
    for(i = 0; i < targets.length; i++) {
        addItem(targets[i][0], targets[i][1], i, "dollar");
    }
}

function addObstacles(quantity) {
    generateObstacleCoordinates(quantity);
    for(i = 0; i < obstacles.length; i++) {
        addItem(obstacles[i][0], obstacles[i][1], i, "rock");
    }
}

function generateTargetCoordinates(quantity) {
    while(targets.length < quantity) {
        y = Math.floor(Math.random() * 10);
        x = Math.floor(Math.random() * 20);
        if(validItemLocation(y,x)) {
            targets.push([y,x]);
        }
    }
}

function generateObstacleCoordinates(quantity) {
    while(obstacles.length < quantity) {
        y = Math.floor(Math.random() * 10);
        x = Math.floor(Math.random() * 20);
        if(validItemLocation(y,x)) {
            obstacles.push([y,x]);
        }
    }
}

function validItemLocation(y, x) {
    if(coordinates.y == y && coordinates.x == x) {
        return false;
    }
    for(i = 0; i < targets.length; i++) {
        if(targets[i][0] == y && targets[i][1] == x) {
            return false;
        }
    }
    for(i = 0; i < obstacles.length; i++) {
        if(obstacles[i][0] == y && obstacles[i][1] == x) {
            return false;
        }
    }
    return true;
}

function addItem(y, x, id, type) {
    y_coord = y * 50;
    x_coord = x * 50;
    var img = document.createElement("img");
    img.style.top = y_coord + "px";
    img.style.left = x_coord + "px";
    img.src = "web/img/" + type + ".png";
    var src = document.getElementById("map");
    src.appendChild(img);
    img.id = "img" + y + x;
    $("#img" + y + x).rotate(Math.floor(Math.random() * 360));
}

function makeTextMap() {
    map = [];
    for(i = 0; i < 10; i++) {
        var row = [];
        for(j = 0; j < 20; j++) {
            row.push(0);
        }
        map.push(row);
    }
    // map[coordinates.y][coordinates.x] = "x";
    for(i = 0; i < targets.length; i++) {
        map[targets[i][0]][targets[i][1]] = 1;
    }
    for(i = 0; i < obstacles.length; i++) {
        map[obstacles[i][0]][obstacles[i][1]] = -1;
    }
    return map;
}

function mapToString(block) {
    str = coordinates.y + "%20" + coordinates.x + "%20";
    for(i = 0; i < 10; i++) {
        if(block) {
            str = str + "\n" + map[i].join("\t");
        } else {
            str = str + map[i].join("%20") + "%20";
        }
    }
    return str;
}
